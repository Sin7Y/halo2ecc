// Decompose an Fp element into bitwise byte chucks

use std::marker::PhantomData;
use crate::utils::*;
use crate::types::Number;
use std::convert::TryFrom;
use ff::PrimeFieldBits;
use crate::testchip::*;

use halo2::{
    arithmetic::FieldExt,
    circuit::{Chip, Layouter, SimpleFloorPlanner, Region},
    dev::{MockProver, VerifyFailure},
    pasta::Fp,
    plonk::{
        Advice, Circuit, Column, ConstraintSystem,
        Error, Expression, Selector, TableColumn
    },
    poly::Rotation,
};


#[derive(Clone, Debug)]
pub struct DecomposeConfig<F:FieldExt + PrimeFieldBits> {
    pub c: Column<Advice>,
    remainder: Column<Advice>,
    sum: Column<Advice>,
    b: Column<Advice>,
    s: Selector,
    tbl_d: TableColumn,
    _marker: PhantomData<F>,
}

struct DecomposeChip<F:FieldExt + PrimeFieldBits> {
    config: DecomposeConfig<F>,
}

impl<F:FieldExt + PrimeFieldBits> Chip<F> for DecomposeChip<F> {
    type Config = DecomposeConfig<F>;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F:FieldExt + PrimeFieldBits> DecomposeChip<F> {
    fn constructor(config: DecomposeConfig<F>) -> Self {
        DecomposeChip { config }
    }

    fn configure(cs: &mut ConstraintSystem<Fp>,
            tbl_d:TableColumn, //domain of table
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
            let r_next = meta.query_advice(r, Rotation::next());
            let b_next = meta.query_advice(b, Rotation::next());
            let sum_next = meta.query_advice(b, Rotation::next());

            let v = c_cur.clone() - c_next * to_expr(256);
            vec![
                sum_next - sum_cur - (r_cur.clone() * b_cur.clone()),
                b_next - b_cur * to_expr(2),
                s * (r_cur - v)
            ]
        });
        DecomposeConfig { c, s, remainder:r, sum, b, tbl_d, _marker: PhantomData }
    }

    fn load_range_table(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
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

    fn decompose(
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
                for idx in 0..num_chunks {
                    config.s.enable(&mut region, idx)?;
                }
                let i = input.clone();
                let mut r = i.clone().value.unwrap();
                let chunks:Vec<u64> = decompose_eight_bits::<F>(r, num_chunks); // little endian
                let two_pow_k_inv = F::from_u64(256 as u64).invert().unwrap();
                let mut v = input.clone();
                let mut b = F::one();
                let mut sum = F::zero();
                region.assign_advice (
                  || format! ("s_{:?}", 0),
                  config.sum,
                  0,
                  || Ok(F::zero())
                )?;
                let init_cell = region.assign_advice (
                  || format! ("c_{:?}", 0),
                  config.c,
                  0,
                  || Ok(r)
                )?;
                region.constrain_equal (i.clone().cell, init_cell);
                region.assign_advice (
                  || format! ("b_{:?}", 0),
                  config.b,
                  0,
                  || Ok(b)
                )?;
                println!("omg ?");
                for (p, chunk) in chunks.iter().enumerate() {
                        let chunk_fp = F::from_u64(u64::try_from(*chunk).unwrap());
                        let chunk_next = (r - chunk_fp) * two_pow_k_inv;
                        sum = chunk_fp * b + sum;
                        println!("{:?} - {:?} - {:?}", chunk_fp, chunk_next, b);
                        region.assign_advice (
                          || format! ("b_{:?}", p + 1),
                          config.b,
                          p + 1,
                          || Ok(F::from_u64(2) * b)
                        )?;
                        region.assign_advice (
                          || format!("r_{:?}", p + 1),
                          config.remainder,
                          p,
                          || Ok(chunk_fp)
                        )?;
                        let carry_cell = region.assign_advice (
                          || format!("c_{:?}", p + 1),
                          config.c,
                          p + 1,
                          || Ok(chunk_next)
                        )?;
                        let cell = region.assign_advice (
                          || format!("s_{:?}", p+1),
                          config.sum,
                          p+1,
                          || Ok(sum)
                        )?;
                        r = chunk_next;
                    output = Some (Number::<F>{cell, value: Some(sum)});
                    carry = Some (Number::<F>{cell: carry_cell, value: Some(chunk_next)});
                    b = F::from_u64(2) * b;
                };
                Ok(())
            },
        )?;
        Ok((output.unwrap(), carry.unwrap()))
    }
}

#[derive(Clone, Default)]
struct MyCircuit {
    input: Fp,
    output: Fp,
    carry: Fp,
}

#[derive(Clone, Debug)]
struct TestCircConfig {
    pconfig: DecomposeConfig<Fp>,
    tconfig: TestConfig,
}

impl Circuit<Fp> for MyCircuit {
    type Config = TestCircConfig ;
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
        let output_cell = test_chip.load_private(layouter.namespace(|| "cell"), Some(self.input))?;
        let carry_cell = test_chip.load_private(layouter.namespace(|| "cell"), Some(self.input))?;
        let chip = DecomposeChip::<Fp>::constructor(config.pconfig);
        println!("loading range table ...");
        //chip.load_range_table(&mut layouter);
        println!("assign region ...");
        chip.decompose(&mut layouter, input_cell.clone(),10)?;
        Ok(())
    }
}

#[test]
fn check() {
    use halo2::dev::MockProver;
    // The number of rows used in the constraint system matrix.
    const PUB_INPUT: u64 = 3;

    let mut pub_inputs = vec![Fp::from(6)];

    let circuit = MyCircuit {
        input: Fp::from(1),
        carry: Fp::from(2),
        output: Fp::from(3),
    };
    let prover = MockProver::run(5, &circuit, vec![pub_inputs]).unwrap();
    let presult = prover.verify();
    println!("Error {:?}", presult);

    assert!(presult.is_ok());
}
