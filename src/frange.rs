// FRange an Fp element into bitwise byte chucks

use crate::testchip::*;
use crate::types::{Number, Fs};
use crate::utils::*;
use crate::byteoptable::*;
use std::marker::PhantomData;
use std::convert::TryInto;

use halo2::{
    arithmetic::FieldExt,
    circuit::{Chip, Layouter, SimpleFloorPlanner},
    pasta::{Fq},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Selector, TableColumn},
    poly::Rotation,
};

#[derive(Clone, Debug)]
pub struct FRangeConfig<Fp: FieldExt, Fr: FieldExt> {
    pub c: Column<Advice>,
    remainder: Column<Advice>,
    sless: Column<Advice>,
    hint: Column<Advice>,
    shift: Column<Advice>,
    s: Selector,
    tbl_v: TableColumn,
    tbl_s: TableColumn,
    tbl_i: TableColumn,
    tbl_o: TableColumn,
    _r_marker: PhantomData<Fr>,
    _p_marker: PhantomData<Fp>
}

pub struct FRangeChip<Fp:FieldExt, Fr: FieldExt> {
    config: FRangeConfig<Fp, Fr>,
}

impl<Fp:FieldExt, F: FieldExt> Chip<F> for FRangeChip<Fp, F> {
    type Config = FRangeConfig<Fp, F>;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<Fp: FieldExt, F: FieldExt> FRangeChip<Fp, F> {
    pub fn constructor(config: FRangeConfig<Fp, F>) -> Self {
        FRangeChip { config }
    }

    fn get_sless_hint (&self, last_is_sless:usize, rem:usize, shift:usize) -> usize {
        let modulus = fp_modulus_on_big_uint::<Fp>();
        let chunk = proj_byte(&modulus, shift);
        if rem < chunk {
            1 as usize
        } else {
            if rem > chunk {
                0 as usize
            } else {
                last_is_sless
            }
        }
    }

    pub fn configure(
        cs: &mut ConstraintSystem<F>,
        tbl_v: TableColumn, //domain of table
        tbl_s: TableColumn, //shift
        tbl_i: TableColumn, //strict less
        tbl_o: TableColumn, //lookup output
    ) -> FRangeConfig<Fp, F> {
        let c = cs.advice_column();
        let r = cs.advice_column();
        let hint = cs.advice_column();
        let shift = cs.advice_column();
        let sless = cs.advice_column();
        let s = cs.selector();

        cs.enable_equality(c.into());
        cs.enable_equality(r.into());
        cs.enable_equality(sless.into());

        // Make sure the remainder does not overflow so that it
        // equals a range check of each remainder
        cs.lookup(|meta| {
            let r_cur = meta.query_advice(r, Rotation::cur());
            let hint_cur = meta.query_advice(hint, Rotation::cur());
            let shift_cur = meta.query_advice(shift, Rotation::cur());
            let sless_cur = meta.query_advice(sless, Rotation::cur());
            vec![(r_cur, tbl_v),
                (hint_cur, tbl_i),
                (shift_cur, tbl_s),
                (sless_cur, tbl_o),
            ]
        });

        cs.create_gate("range check", |meta| {
            //
            // | c       | remainder      | hint | shift | strict_less
            // | c_cur   | remainder_cur  | 0    | s     | less_lookup_cur
            // | c_next  | remainder_next | enc  | s + 1 | less_lookup_next
            // .....
            // | c_final |                | hint | ...   | strict_less_final
            //
            let s = meta.query_selector(s);
            let c_cur = meta.query_advice(c, Rotation::cur());
            let r_cur = meta.query_advice(r, Rotation::cur());
            let sless_cur = meta.query_advice(sless, Rotation::cur());
            let shift_cur = meta.query_advice(sless, Rotation::cur());

            let c_next = meta.query_advice(c, Rotation::next());
            let hint_next = meta.query_advice(hint, Rotation::next());
            let shift_next = meta.query_advice(sless, Rotation::next());

            let v = c_cur.clone() - c_next * to_expr(256);
            vec![
                s.clone() * (shift_next - shift_cur - to_expr(1)),
                s.clone() * (hint_next - sless_cur),
                s.clone() * (r_cur - v),
            ]
        });

        FRangeConfig {
            c,
            s,
            remainder: r,
            hint,
            shift,
            sless,
            tbl_v,
            tbl_s,
            tbl_i,
            tbl_o,
            _r_marker: PhantomData,
            _p_marker: PhantomData,
        }
    }

    pub fn frange_check(
        &self,
        layouter: &mut impl Layouter<F>,
        input: Fs<F>,
    ) -> Result<(), Error> {
        let (sless0, carry0) = self.check (layouter, input.values[0], 0, 0, 10)?;
        let (sless1, carry1) = self.check (layouter, input.values[0], 0, 10, 10)?;
        let (sless2, carry2) = self.check (layouter, input.values[0], 0, 20, 12)?;
        Ok(())
    }


    pub fn check (
        &self,
        layouter: &mut impl Layouter<F>,
        input: Number<F>,
        sless: usize,
        start: usize,
        num_chunks: usize,
    ) -> Result<(Number<F>, Number<F>), Error> {
        let mut output = None;
        let mut carry = None;
        layouter.assign_region(
            || "load private",
            |mut region| {
                let config = self.config();

                for row in 0..num_chunks {
                    config.s.enable(&mut region, row)?;
                }

                let bytes = input.value.unwrap().to_bytes();
                let mut shift = start;
                let mut c = input.clone().value.unwrap();
                let mut hint = sless;

                for row in 0..num_chunks + 1 {
                    let rem =
                        if row != num_chunks {
                            F::from_u64(bytes[row].into())
                        } else {
                            F::zero()
                        };

                    let c_cell =
                        region.assign_advice(|| format!("c_{:?}", 0), config.c, row, || Ok(c))?;

                    if row == 0 {
                        region.constrain_equal(input.cell, c_cell)?;
                    }

                    region.assign_advice(|| format!("shift_{:?}", row),
                        config.shift,
                        row,
                        || Ok(F::from_u64(shift.try_into().unwrap()))
                    )?;

                    region.assign_advice(
                        || format!("rem_{:?}", row),
                        config.remainder,
                        row,
                        || Ok(rem),
                    )?;

                    region.assign_advice(
                        || format!("hint_{:?}", row),
                        config.hint,
                        row,
                        || Ok(F::from_u64(sless.try_into().unwrap())),
                    )?;

                    hint = self.get_sless_hint(hint, bytes[row].into(), shift);
                    let sless_cell = region.assign_advice(
                        || format!("sless_{:?}", row),
                        config.sless,
                        row,
                        || Ok(F::from_u64(hint.try_into().unwrap())),
                    )?;

                    if row == num_chunks {
                        output = Some(Number::<F>{
                            cell: sless_cell,
                            value: Some(F::from_u64(hint.try_into().unwrap()))
                        });
                        carry = Some(Number::<F>{cell: c_cell, value: Some(c)});
                    }
                    shift += 1;
                    c = n_div_256(c);
                }

                Ok(())
            },
        )?;
        Ok((output.unwrap(), carry.unwrap()))
    }
}

#[derive(Clone, Default)]
struct MyCircuit<F: FieldExt> {
    input: F,
    chunk_size: usize,
}

#[derive(Clone, Debug)]
struct CircuitConfig<F: FieldExt> {
    rangec: FRangeConfig<Fq, F>,
    bopc: ByteOpChipConfig,
    testc: TestConfig,
}

impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
    type Config = CircuitConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(cs: &mut ConstraintSystem<F>) -> Self::Config {
        let bopc = ByteOpChip::<Fq, F, StrictLessOp<F>>::configure(cs);
        let rangec =
            FRangeChip::<Fq, F>::configure(cs, bopc.tbl_l, bopc.tbl_r, bopc.tbl_s, bopc.tbl_o);
        let testc = TestChip::configure(cs);
        return CircuitConfig { rangec, bopc, testc };
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        println!("Start synthesize ...");
        let test_chip = TestChip::<F>::construct(config.testc);
        let input_cell = test_chip.load_private(layouter.namespace(|| "cell"), Some(self.input))?;

        let op_chip = ByteOpChip::<Fq, F, StrictLessOp<F>>::construct(config.bopc);
        op_chip.alloc_table(
            layouter.namespace(|| "less tbl")
        )?;

        let chip = FRangeChip::<Fq,F>::constructor(config.rangec);
        let (sless, carry) = chip.check(&mut layouter, input_cell.clone(), 0, 0, self.chunk_size)?;
        test_chip.expose_public(layouter.namespace(|| "sless"), sless.clone(), 0)?;
        test_chip.expose_public(layouter.namespace(|| "carry"), carry.clone(), 1)?;
        Ok(())
    }
}

#[test]
fn frange_test1() {
    use halo2::dev::MockProver;

    let q_modulus = fp_modulus_on_big_uint::<Fq>();

    let q_minus_1 = q_modulus - 1u64;

    let x0 = proj_big_uint::<Fp> (&q_minus_1, 0);
    let x1 = proj_big_uint::<Fp> (&q_minus_1, 1);
    let x2 = proj_big_uint::<Fp> (&q_minus_1, 2);

    let circuit = MyCircuit {
        input: x0,
        chunk_size: 10,
    };

    let pub_inputs = vec![Fp::one(), Fp::zero()];
    let prover = MockProver::run(15, &circuit, vec![pub_inputs]).unwrap();
    let presult = prover.verify();
    println!("Error {:?}", presult);

    assert!(presult.is_ok());
}
