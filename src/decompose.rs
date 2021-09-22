// Decompose an Fp element into bitwise byte chucks

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
pub struct DecomposeConfig<F: FieldExt> {
    pub c: Column<Advice>,
    remainder: Column<Advice>,
    sum: Column<Advice>,
    b: Column<Advice>,
    s: Selector,
    tbl_d: TableColumn,
    _marker: PhantomData<F>,
}

pub struct DecomposeChip<F: FieldExt> {
    config: DecomposeConfig<F>,
}

impl<F: FieldExt> Chip<F> for DecomposeChip<F> {
    type Config = DecomposeConfig<F>;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: FieldExt> DecomposeChip<F> {
    pub fn constructor(config: DecomposeConfig<F>) -> Self {
        DecomposeChip { config }
    }

    pub fn configure(
        cs: &mut ConstraintSystem<Fp>,
        tbl_d: TableColumn, //domain of table
    ) -> DecomposeConfig<F> {
        let c = cs.advice_column();
        let r = cs.advice_column();
        let b = cs.advice_column();
        let sum = cs.advice_column();
        let s = cs.selector();

        cs.enable_equality(c.into());
        cs.enable_equality(r.into());
        cs.enable_equality(sum.into());

        // Make sure the remainder does not overflow so that it
        // equals a range check of each remainder
        cs.lookup(|meta| {
            let r_cur = meta.query_advice(r, Rotation::cur());
            vec![(r_cur, tbl_d)]
        });

        cs.create_gate("range check", |meta| {
            //
            // | c_cur   | remainder      | sum      | b
            // | c_next  | remainder_next | sum_next | b_next
            // .....
            // | c_final | <---- remainder = c_cur - c_final * 2^d
            //
            let s = meta.query_selector(s);
            let c_cur = meta.query_advice(c, Rotation::cur());
            let r_cur = meta.query_advice(r, Rotation::cur());
            let b_cur = meta.query_advice(b, Rotation::cur());
            let sum_cur = meta.query_advice(sum, Rotation::cur());

            let c_next = meta.query_advice(c, Rotation::next());
            let b_next = meta.query_advice(b, Rotation::next());
            let sum_next = meta.query_advice(sum, Rotation::next());

            let v = c_cur.clone() - c_next * to_expr(256);
            vec![
                s.clone() * (sum_next - sum_cur - (r_cur.clone() * b_cur.clone())),
                s.clone() * (b_next - b_cur * to_expr(256)),
                s.clone() * (r_cur - v),
            ]
        });

        DecomposeConfig {
            c,
            s,
            remainder: r,
            sum,
            b,
            tbl_d,
            _marker: PhantomData,
        }
    }

    pub fn load_range_table(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        let table_values: Vec<F> = (0..1 << 8).map(|e| F::from_u64(e)).collect();
        layouter.assign_table(
            || "",
            |mut table| {
                for (index, &value) in table_values.iter().enumerate() {
                    table.assign_cell(|| "byte-table", self.config.tbl_d, index, || Ok(value))?;
                }
                Ok(())
            },
        )?;
        Ok(())
    }

    pub fn decompose(
        &self,
        layouter: &mut impl Layouter<F>,
        input: Number<F>,
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
                let mut b = F::from(1);
                let mut c = input.clone().value.unwrap();
                let mut sum = F::zero();

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

                    region.assign_advice(|| format!("shift_{:?}", row), config.b, row, || Ok(b))?;

                    region.assign_advice(
                        || format!("rem_{:?}", row),
                        config.remainder,
                        row,
                        || Ok(rem),
                    )?;

                    let sum_cell = region.assign_advice(
                        || format!("sum_{:?}", row),
                        config.sum,
                        row,
                        || Ok(sum),
                    )?;

                    if row == num_chunks {
                        output = Some(Number::<F>{cell: sum_cell, value: Some(sum)});
                        carry = Some(Number::<F>{cell: c_cell, value: Some(c)});
                    }

                    sum += rem * b;
                    b *= F::from(256);
                    c = n_div_256(c);
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
    pconfig: DecomposeConfig<Fp>,
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
            pconfig: DecomposeChip::<Fp>::configure(cs, table_col),
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
        let chip = DecomposeChip::<Fp>::constructor(config.pconfig);
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
