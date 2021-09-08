extern crate halo2;

use crate::types::{Fs, Number};
use crate::utils::*;
use ff::PrimeFieldBits;
use std::convert::TryFrom;
use std::convert::TryInto;
use std::marker::PhantomData;

use crate::byteoptable::ShiftOpChip;

use halo2::{
    arithmetic::FieldExt,
    circuit::{Chip, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector, TableColumn},
    poly::Rotation,
};

// Suppose that c = a * 2^256. Then it follows that
// after decompose c into 8 bits as [x_i]
// we need to lookup our shift multiplication table to
// calculate x_i' and then sum x_i to get the final result

#[derive(Clone, Debug)]
pub struct ShortMultConfig {
    c: Column<Advice>,
    r: Column<Advice>,
    shift: Column<Advice>,
    lookup: [Column<Advice>; 3],
    sum: [Column<Advice>; 3],
    sel: Selector,
}

pub trait ShortMult<F: FieldExt + PrimeFieldBits>: Chip<F> {
    fn constrain(
        &self,
        layouter: impl Layouter<F>,
        a: Number<F>,
        num_chunks: usize,
        shift_base: u64,
    ) -> Result<(Fs<F>, Number<F>), Error>;
}

pub struct ShortMultChip<Fp: FieldExt, F: FieldExt + PrimeFieldBits> {
    config: ShortMultConfig,
    _marker: PhantomData<F>,
    __marker: PhantomData<Fp>,
}

impl<Fp: FieldExt, F: FieldExt + PrimeFieldBits> ShortMultChip<Fp, F> {
    pub fn construct(config: <Self as Chip<F>>::Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
            __marker: PhantomData,
        }
    }

    pub fn configure(
        cs: &mut ConstraintSystem<F>,
        lookup_v: TableColumn,
        lookup_s: TableColumn,
        lookup_i: TableColumn,
        lookup_o: TableColumn,
    ) -> <Self as Chip<F>>::Config {
        let c = cs.advice_column();
        let r = cs.advice_column();
        let shift = cs.advice_column();
        let lookup = [cs.advice_column(), cs.advice_column(), cs.advice_column()];
        let sum = [cs.advice_column(), cs.advice_column(), cs.advice_column()];
        let sel = cs.selector();

        cs.enable_equality(c.into());
        cs.enable_equality(sum[0].into());
        cs.enable_equality(sum[1].into());
        cs.enable_equality(sum[2].into());

        // Using lookup has side benifits which ensures that
        // remainder does not overflow so that it
        // equals performing a range check of each remainder
        for i in 0..3 {
            cs.lookup(|meta| {
                let r_cur = meta.query_advice(r, Rotation::cur());
                let shift_cur = meta.query_advice(shift, Rotation::cur());
                let lookup_cur = meta.query_advice(lookup[i], Rotation::cur());
                vec![
                    (r_cur, lookup_v),
                    (shift_cur, lookup_s),
                    (lookup_cur, lookup_o),
                    (to_expr(i as u64), lookup_i),
                ]
            });
        }

        cs.create_gate("sum check", |meta| {
            //
            // | c_cur   | remainder_cur  | shift_cur  | lookup_{0,1,2} | sum_{0,1,2} | sel
            // | c_next  | remainder_next | shift_next | ...            | ...
            // .....
            // | c_final |                |            |                |
            //
            let s = meta.query_selector(sel);

            let sum_cur: [Expression<F>; 3] = sum
                .clone()
                .iter()
                .map(|sum| meta.query_advice(*sum, Rotation::cur()))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap();
            let sum_next: [Expression<F>; 3] = sum
                .iter()
                .map(|sum| meta.query_advice(*sum, Rotation::next()))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap();

            let lookup_cur: [Expression<F>; 3] = lookup
                .iter()
                .map(|lookup| meta.query_advice(*lookup, Rotation::cur()))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap();

            vec![
                s.clone() * (sum_next[0].clone() - lookup_cur[0].clone() - sum_cur[0].clone()),
                s.clone() * (sum_next[1].clone() - lookup_cur[1].clone() - sum_cur[1].clone()),
                s.clone() * (sum_next[2].clone() - lookup_cur[2].clone() - sum_cur[2].clone()),
            ]
        });

        cs.create_gate("shift check", |meta| {
            //
            // | c_cur   | remainder_cur  | shift_cur  | lookup_{0,1,2} | sum_{0,1,2} | sel
            // | c_next  | remainder_next | shift_next | ...            | ...
            // .....
            // | c_final |                |            |                |
            //
            let s = meta.query_selector(sel);

            let shift_cur = meta.query_advice(shift, Rotation::cur());
            let shift_next = meta.query_advice(shift, Rotation::next());

            vec![
                s.clone() * (shift_next - shift_cur - to_expr(1)), // inc the shift amount
            ]
        });

        cs.create_gate("rem check", |meta| {
            //
            // | c_cur   | remainder_cur  | shift_cur  | lookup_{0,1,2} | sum_{0,1,2} | sel
            // | c_next  | remainder_next | shift_next | ...            | ...
            // .....
            // | c_final |                |            |                |
            //
            let s = meta.query_selector(sel);

            let c_cur = meta.query_advice(c, Rotation::cur());
            let c_next = meta.query_advice(c, Rotation::next());
            let r_cur = meta.query_advice(r, Rotation::cur());

            vec![
                s.clone() * (c_cur - c_next * to_expr(256) - r_cur), // restrict the remainder
            ]
        });

        ShortMultConfig {
            c,
            r,
            shift,
            lookup,
            sum,
            sel,
        }
    }

    fn assign_region(
        &self,
        mut layouter: impl Layouter<F>,
        input: Number<F>,
        num_chunks: usize,
        shift_base: u64,
    ) -> Result<(Fs<F>, Number<F>), Error> {
        let config = self.config();

        let mut final_sum = [input.clone(), input.clone(), input.clone()];
        let mut final_c = input.clone();

        //
        // | c_cur   | remainder_cur  | shift_cur  | lookup_{0,1,2} | sum_{0,1,2} | sel
        // | c_next  | remainder_next | shift_next | ...            | ...
        // .....
        // | c_final |                |            |                |
        //
        layouter.assign_region(
            || "smult",
            |mut region| {
                for row in 0..num_chunks {
                    config.sel.enable(&mut region, row)?;
                }
                for row in 0..num_chunks + 1 {
                    region.assign_advice(
                        || format!("shift_{:?}", row),
                        config.shift,
                        row,
                        || Ok(F::from_u64(row as u64 + shift_base)),
                    )?;
                }

                // For c, rem, lookup, sum
                let bytes = input.value.unwrap().to_bytes();
                let mut c = input.clone().value.unwrap();
                let mut sum = [F::zero(), F::zero(), F::zero()];

                for row in 0..num_chunks {
                    let _rem = F::from_u64(bytes[row].into());
                    let rem = Fp::from_u64(bytes[row].into());

                    let lookup = get_shift_lookup(rem, shift_base + row as u64);
                    println!("shift {} ", shift_base);
                    println!("rem {} {:?}", row, rem);

                    let c_cell =
                        region.assign_advice(|| format!("c_{:?}", 0), config.c, row, || Ok(c))?;

                    if row == 0 {
                        region.constrain_equal(input.cell, c_cell)?;
                    }

                    region.assign_advice(
                        || format!("rem_{:?}", row),
                        config.r,
                        row,
                        || Ok(_rem),
                    )?;

                    for i in 0..3 {
                        let lookupi: F = projF(lookup, i);
                        region.assign_advice(
                            || format!("lookup_{:?}_{:?}", i, row),
                            config.lookup[i],
                            row,
                            || Ok(lookupi),
                        )?;

                        println!("lookupi {} {} {:?}", row, i, lookupi);
                        region.assign_advice(
                            || format!("sum_{:?}_{:?}", i, row),
                            config.sum[i],
                            row,
                            || Ok(sum[i]),
                        )?;

                        println!("sum {} {} {:?}", row, i, sum[i]);
                        sum[i] += lookupi;
                    }

                    c = N_div_256(c);
                }

                // last row
                final_c.cell = region.assign_advice(
                    || format!("c_{:?}", num_chunks),
                    config.c,
                    num_chunks,
                    || Ok(c),
                )?;

                final_c.value = Some(c);

                region.assign_advice(
                    || format!("rem_{:?}", num_chunks),
                    config.r,
                    num_chunks,
                    || Ok(F::zero()),
                )?;

                for i in 0..3 {
                    final_sum[i].cell = region.assign_advice(
                        || format!("sum_{:?}_{:?}", i, num_chunks),
                        config.sum[i],
                        num_chunks,
                        || Ok(sum[i]),
                    )?;

                    final_sum[i].value = Some(sum[i]);

                    region.assign_advice(
                        || format!("lookup_{:?}_{:?}", i, num_chunks),
                        config.lookup[i],
                        num_chunks,
                        || Ok(F::zero()),
                    )?;
                }

                Ok(())
            },
        )?;

        Ok((Fs::<F> { values: final_sum }, final_c))
    }
}

impl<Fp: FieldExt, F: FieldExt + PrimeFieldBits> Chip<F> for ShortMultChip<Fp, F> {
    type Config = ShortMultConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<Fp: FieldExt, F: FieldExt + PrimeFieldBits> ShortMult<F> for ShortMultChip<Fp, F> {
    fn constrain(
        &self,
        layouter: impl Layouter<F>,
        a: Number<F>,
        num_chunks: usize,
        shift_base: u64,
    ) -> Result<(Fs<F>, Number<F>), Error> {
        self.assign_region(layouter, a, num_chunks, shift_base)
    }
}

#[derive(Default)]
struct MyCircuit<F: FieldExt + PrimeFieldBits> {
    input: Option<F>,
}

use crate::byteoptable::*;
use crate::testchip::*;
use halo2::circuit::SimpleFloorPlanner;
use halo2::pasta::{Fp, Fq};
use halo2::plonk::Circuit;

#[derive(Clone, Debug)]
pub struct CircuitConfig {
    smult: ShortMultConfig,
    bopc: ByteOpChipConfig,
    testc: TestConfig,
}

const CHUNCK_BITS: usize = 8;
const L_RANGE: usize = 1 << CHUNCK_BITS;
const R_RANGE: usize = 256 * 2 / CHUNCK_BITS;
const S_RANGE: usize = 3;

impl<F: FieldExt + PrimeFieldBits> Circuit<F> for MyCircuit<F> {
    // Since we are using a single chip for everything, we can just reuse its config.
    type Config = CircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }
    fn configure(cs: &mut ConstraintSystem<F>) -> Self::Config {
        let bopc = ByteOpChip::<F, Fq, ShiftOp>::configure(cs);
        let smult =
            ShortMultChip::<Fq, F>::configure(cs, bopc.tbl_l, bopc.tbl_r, bopc.tbl_s, bopc.tbl_o);
        let testc = TestChip::configure(cs);
        return CircuitConfig { smult, bopc, testc };
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let test_chip = TestChip::construct(config.testc);
        let input = test_chip.load_private(layouter.namespace(|| "load"), self.input)?;

        let op_chip = ByteOpChip::<F, Fq, ShiftOp>::construct(config.bopc);
        op_chip.alloc_table(
            layouter.namespace(|| "shift tbl"),
            L_RANGE,
            R_RANGE,
            S_RANGE,
        )?;

        let smult_chip = ShortMultChip::<Fq, F>::construct(config.smult);
        let out = smult_chip.constrain(layouter.namespace(|| "smult"), input, 10, 0)?;
        println!("out is {:?}", out);
        test_chip.expose_public(layouter.namespace(|| "out0"), out.0.values[0].clone(), 0)?;
        test_chip.expose_public(layouter.namespace(|| "out1"), out.0.values[1].clone(), 1)?;
        test_chip.expose_public(layouter.namespace(|| "out2"), out.0.values[2].clone(), 2)?;
        test_chip.expose_public(layouter.namespace(|| "out3"), out.1.clone(), 3)?;

        Ok(())
    }
}
// ANCHOR_END: circuit

#[test]
fn main1() {
    use halo2::{dev::MockProver, pasta::Fp};
    let k = 17;

    // let input = Some(Fp::from(400)); // 256 + 144
    let input = Some(Fp::from(0)); // 256 + 144

    let circuit = MyCircuit { input };

    let mut public_inputs = vec![
        Fp::from_u128(0),
        Fp::from_u128(0),
        //    Fp::from_u128(483570327845851669882470400u128),
        Fp::from_u128(0),
        Fp::from_u128(0),
    ];

    let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
    assert_eq!(prover.verify(), Ok(()));

    public_inputs[0] += Fp::one();
    let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();
    assert!(prover.verify().is_err());
}

#[test]
fn main2() {
    use halo2::{dev::MockProver, pasta::Fp};
    let k = 17;

    let input = Some(Fp::from(400)); // 256 + 144

    let circuit = MyCircuit { input };

    let mut public_inputs = vec![
        Fp::from_u128(0),
        Fp::from_u128(0),
        Fp::from_u128(483570327845851669882470400u128),
        Fp::from_u128(0),
    ];

    let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
    assert_eq!(prover.verify(), Ok(()));

    public_inputs[0] += Fp::one();
    let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();
    assert!(prover.verify().is_err());
}
