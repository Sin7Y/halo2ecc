// FRange an Fp element into bitwise byte chucks

use crate::testchip::*;
use crate::types::Number;
use crate::utils::*;
use std::marker::PhantomData;

use halo2::{
    arithmetic::FieldExt,
    circuit::{Chip, Layouter, SimpleFloorPlanner},
    pasta::Fp,
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Selector, TableColumn},
    poly::Rotation,
};

#[derive(Clone, Debug)]
pub struct FRangeConfig<F: FieldExt> {
    pub c: Column<Advice>,
    remainder: Column<Advice>,
    sum: Column<Advice>,
    b: Column<Advice>,
    s: Selector,
    tbl_v: TableColumn,
    tbl_s: TableColumn,
    tbl_i: TableColumn,
    tbl_o: TableColumn,
    _marker: PhantomData<F>,
}

pub struct FRangeChip<F: FieldExt> {
    config: FRangeConfig<F>,
}

impl<F: FieldExt> Chip<F> for FRangeChip<F> {
    type Config = FRangeConfig<F>;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: FieldExt> FRangeChip<F> {
    pub fn constructor(config: FRangeConfig<F>) -> Self {
        FRangeChip { config }
    }

    fn get_sless_hint (&self, last_is_sless:u64, rem:u64, shift:usize) -> u64 {
        let config = self.config();
        if (rem < self.chuncks[usize]) {
            1 as u64
        } else {
            if (rem > self.chunks[usize]) {
                0 as u64
            } else {
                last_is_sless
            }
        }
    }

    pub fn configure(
        cs: &mut ConstraintSystem<Fp>,
        tbl_v: TableColumn, //domain of table
        tbl_s: TableColumn, //shift
        tbl_i: TableColumn, //strict less
        tbl_o: TableColumn, //lookup output
    ) -> FRangeConfig<F> {
        let c = cs.advice_column();
        let r = cs.advice_column();
        let hint = cs.advice_column();
        let shift = cs.advice_column();
        let sless = cs.advice_column();
        let s = cs.selector();

        cs.enable_equality(c.into());
        cs.enable_equality(r.into());
        cs.enable_equality(sum.into());

        // Make sure the remainder does not overflow so that it
        // equals a range check of each remainder
        cs.lookup(|meta| {
            let r_cur = meta.query_advice(r, Rotation::cur());
            let hint_cur = meta.query_advice(shift, Rotation::cur());
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
            let hint_cur = meta.query_advice(hint, Rotation::cur());
            let sless_cur = meta.query_advice(sless, Rotation::cur());
            let shift_cur = meta.query_advice(sless, Rotation::cur());

            let c_next = meta.query_advice(c, Rotation::next());
            let r_next = meta.query_advice(r, Rotation::next());
            let hint_next = meta.query_advice(hint, Rotation::next());
            let shift_next = meta.query_advice(sless, Rotation::next());

            let v = c_cur.clone() - c_next * to_expr(256);
            vec![
                s.clone() * (sum_next - sum_cur - (r_cur.clone() * b_cur.clone())),
                s.clone() * (shift_next - shift_cur - 1),
                s.clone() * (hint_next - (sless_cur + (shfit * to_expr(2)))),
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
            _marker: PhantomData,
        }
    }

    pub fn decompose(
        &self,
        layouter: &mut impl Layouter<F>,
        input: Number<F>,
        sless: F,
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
                let mut shift = F::from_u64(start.try_into().unwrap());
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

                    region.assign_advice(|| format!("shift_{:?}", row), config.shift, row, || Ok(shift))?;

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
                        || Ok(sless),
                    )?;

                    let sless = self.get_sless_hint(sless, bytes[row].into(), shift);
                    let sless_cell = region.assign_advice(
                        || format!("sless_{:?}", row),
                        config.sless,
                        row,
                        || Ok(sless),
                    )?;

                    if row == num_chunks {
                        output = Some(Number::<F>{cell: sless_cell, value: Some(sless)});
                        carry = Some(Number::<F>{cell: c_cell, value: Some(c)});
                    }
                    shift += 1;
                    c = N_div_256(c);
                }

                Ok(())
            },
        )?;
        Ok((output.unwrap(), carry.unwrap()))
    }
}

#[derive(Clone, Default)]
struct MyCircuit {
    input: Fp,
    chunk_size: usize,
}

#[derive(Clone, Debug)]
struct TestCircConfig {
    pconfig: FRangeConfig<Fp>,
    tconfig: TestConfig,
}

impl Circuit<Fp> for MyCircuit {
    type Config = TestCircConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(cs: &mut ConstraintSystem<Fp>) -> Self::Config {
        let table_col = cs.lookup_table_column();
        println!("configure done!");
        TestCircConfig {
            pconfig: FRangeChip::<Fp>::configure(cs, table_col),
            tconfig: TestChip::<Fp>::configure(cs),
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fp>,
    ) -> Result<(), Error> {
        println!("Start synthesize ...");
        let test_chip = TestChip::<Fp>::construct(config.tconfig);
        let input_cell = test_chip.load_private(layouter.namespace(|| "cell"), Some(self.input))?;
        let chip = FRangeChip::<Fp>::constructor(config.pconfig);
        println!("loading range table ...");

        chip.load_range_table(&mut layouter)?;
        println!("assign region ...");
        let (sum, carry) = chip.decompose(&mut layouter, input_cell.clone(), self.chunk_size)?;
        test_chip.expose_public(layouter.namespace(|| "out"), sum, 0)?;
        test_chip.expose_public(layouter.namespace(|| "out"), carry, 1)?;
        Ok(())
    }
}

#[test]
fn test1() {
    use halo2::dev::MockProver;
    let pub_inputs = vec![Fp::from(0x3456), Fp::from(0x12)];

    let circuit = MyCircuit {
        input: Fp::from(0x123456),
        chunk_size: 2,
    };
    let prover = MockProver::run(9, &circuit, vec![pub_inputs]).unwrap();
    let presult = prover.verify();
    println!("Error {:?}", presult);

    assert!(presult.is_ok());
}

#[test]
fn test2() {
    use halo2::dev::MockProver;
    // The number of rows used in the constraint system matrix.
    const PUB_INPUT: u64 = 3;

    let pub_inputs = vec![Fp::from(0x2), Fp::from(0x0)];

    let circuit = MyCircuit {
        input: Fp::from(0x2),
        chunk_size: 10,
    };
    let prover = MockProver::run(9, &circuit, vec![pub_inputs]).unwrap();
    let presult = prover.verify();
    println!("Error {:?}", presult);

    assert!(presult.is_ok());
}
