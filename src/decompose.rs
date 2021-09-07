// Decompose an Fp element into bitwise byte chucks

use std::marker::PhantomData;
use crate::utils::*;
use crate::types::Number;
use std::convert::TryFrom;
use ff::PrimeFieldBits;

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
    basis: Column<Advice>,
    s: Selector,
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
        let s = cs.selector();

        // Make sure the remainder does not overflow so that it
        // equals a range check of each remainder
        cs.lookup(|meta| {
          let r_cur = meta.query_advice(r, Rotation::cur());
          vec![(r_cur, tbl_d)]
        });

        cs.create_gate("range check", |meta| {
            //
            // | c_cur   | remainder      | basis
            // | c_next  | remainder_next | basis_next
            // .....
            // | c_final | <---- remainder = c_cur - c_final * 2^d
            //
            let s = meta.query_selector(s);
            let c_cur = meta.query_advice(c, Rotation::cur());
            let r_cur = meta.query_advice(r, Rotation::cur());
            let b_cur = meta.query_advice(b, Rotation::cur());

            let c_next = meta.query_advice(c, Rotation::next());
            let r_next = meta.query_advice(r, Rotation::next());
            let b_next = meta.query_advice(b, Rotation::next());

            let v = c_cur - c_next * to_expr(4);
            vec![b_next - b_cur * to_expr(2), r_cur - v]
        });

        DecomposeConfig { c, s, remainder:r, basis:b, _marker: PhantomData }
    }

    fn decompose(
        &self,
        input: Number<F>,
        region: &mut Region<'_, F>,
        num_chunks: usize,
        chunk_size: usize, // how many bits for each chunk
    ) -> Result<Vec<Number<F>>, Error> {
        let config = self.config();
        for idx in 0..num_chunks {
            config.s.enable(region, idx)?;
        }
        let i = input.clone();
        let mut r = i.clone().value.unwrap();
        let chunks:Vec<u8> = decompose_four_bits::<F>(r, chunk_size*num_chunks); // little endian
        let mut output = vec![input.clone()];
        let two_pow_k_inv = F::from_u64(4 as u64).invert().unwrap();
        let mut v = input;

        for (p, chunk) in chunks.iter().enumerate() {
            let v_next = {
                let chunk_fp = F::from_u64(u64::try_from(*chunk).unwrap());
                let chunk_next = (r - chunk_fp) * two_pow_k_inv;
                let cell = region.assign_advice (
                  || format!("n_{:?}", p + 1),
                  config.c,
                  p + 1,
                  || Ok(chunk_next)
                )?;
                r = chunk_next;
                Number::<F>{cell, value: Some(chunk_next)}
            };
            v = v_next;
            output.push(v);
        }
        Ok(output)
    }
}
/*
// Allocates `a` and ensures that it is contained within the range `[RANGE_FIRST, RANGE_LAST]`.
#[derive(Clone, Default)]
struct MyCircuit {
    // Private input.
    a: Option<Fp>,
}

impl Circuit<Fp> for MyCircuit {
    type Config = DecomposeConfig<Fp> ;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(cs: &mut ConstraintSystem<Fp>) -> Self::Config {
        DecomposeConfig::configure(cs)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fp>,
    ) -> Result<(), Error> {
        let chip = DecomposeChip::new(config);
        Ok(());
        //chip.decompose(&mut layouter, self.a)
    }
}

#[test]
fn check() {
    // The number of rows utilized in the constraint system matrix.
    const N_ROWS_USED: u32 = 1;

    // `k` can be zero, which is the case when `N_ROWS_USED = 1`.
    //let k = (N_ROWS_USED as f32).log2().ceil() as u32;
    let k = 4;
    // This circuit has no public inputs.
    let pub_inputs = vec![Fp::zero(); 1 << k];

    // Assert that the constraint system is satisfied when `a ∈ [RANGE_FIRST, RANGE_LAST]`.
    for a in RANGE_FIRST..=RANGE_LAST {
        let circuit = MyCircuit { a: Some(Fp::from(a)) };
        let prover = MockProver::run(k, &circuit, vec![pub_inputs.clone()])
            .expect("failed to synthesize circuit");
        assert!(prover.verify().is_ok());
    }

    // Assert that the constraint system is not satisfied when `a ∉ [RANGE_FIRST, RANGE_LAST]`.
    for bad_a in &[RANGE_FIRST - 1, RANGE_LAST + 1] {
        let bad_circuit = MyCircuit { a: Some(Fp::from(*bad_a)) };
        let prover = MockProver::run(k, &bad_circuit, vec![pub_inputs.clone()])
            .expect("failed to synthesize circuit");
        match prover.verify() {
            Err(errors) => {
                assert_eq!(errors.len(), 1, "expected one verification error, found: {:?}", errors);
                match &errors[0] {
                    VerifyFailure::Cell { .. } => {}
                    err => panic!("expected 'range check' gate failure, found: {:?}", err),
                }
            }
            _ => panic!("expected `prover.verify()` to return an error for `a = {}`", bad_a),
        };
    }
}
*/


