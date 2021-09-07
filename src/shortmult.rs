#![feature(array_map)]
extern crate halo2;

use std::marker::PhantomData;
use crate::types::Number;
use crate::utils::*;
use crate::decompose::*;
use std::convert::TryFrom;
use ff::{PrimeFieldBits};

use halo2::{
    arithmetic::FieldExt,
    circuit::{Cell, Chip, Layouter, Region, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance, TableColumn, Selector},
    poly::Rotation,
};

// Short Multiplication for a * b:
// let c = a * b then after decompose c into 12 bits as [x_i] we need to lookup table to
// calculate x_i' and then sum x_i to get the final result

#[derive(Clone, Debug)]
struct ShortMultConfig {
    c: Column<Advice>,
    r: Column<Advice>,
    shift: Column<Advice>,
    out: [Column<Advice>;3],
    sum: [Column<Advice>;3],
    sel: Selector,
}

trait ShortMult <F: FieldExt + PrimeFieldBits>: Chip<F> {
    fn mult (
        &self,
        layouter: impl Layouter<F>,
        a: Number<F>,
        b: Number<F>,
    ) -> Result<Number<F>, Error>;
}

struct ShortMultChip<F: FieldExt + PrimeFieldBits> {
    config: ShortMultConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt + PrimeFieldBits> ShortMultChip<F> {
    fn construct(config: <Self as Chip<F>>::Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn configure(
        cs: &mut ConstraintSystem<F>,
        lookup_v: TableColumn,
        lookup_s: TableColumn,
        lookup_i: TableColumn,
        lookup_o: TableColumn,
    ) -> <Self as Chip<F>>::Config {
        let c = cs.advice_column();
        let r = cs.advice_column();
        let shift = cs.advice_column();
        let out = [cs.advice_column(), cs.advice_column(), cs.advice_column()];
        let sum = [cs.advice_column(), cs.advice_column(), cs.advice_column()];
        let sel = cs.selector();

        // Make sure the remainder does not overflow so that it
        // equals a range check of each remainder
        cs.lookup(|meta| {
          let r_cur = meta.query_advice(r, Rotation::cur());
          let shift_cur = meta.query_advice(shift, Rotation::cur());
          let out_cur = meta.query_advice(out[0], Rotation::cur());
          vec![(r_cur, lookup_v), (shift_cur, lookup_s), (out_cur, lookup_o), (to_expr(0), lookup_i)]
        });
        /*
        cs.create_gate("range check", |meta| {
            //
            // | c_cur   | remainder      | shift      | l0 | l1 | l2 | sum0 | sum1 | sum2
            // | c_next  | remainder_next | shift_next | l0 | l1 | l2 | sum0 | sum1 | sum2
            // .....
            // | c_final | <- should be zero           |              | sum0 | sum1 | sum2
            //
            let s = meta.query_selector(sel);
            let c_cur = meta.query_advice(c, Rotation::cur());
            let sum_cur = sum.map(|sum| meta.query_advice(sum, Rotation::cur()));
            let out_cur = out.map(|out| meta.query_advice(out, Rotation::cur()));
            let r_cur = meta.query_advice(out, Rotation::cur());
            let shift_cur = meta.query_advice(shift, Rotation::cur());

            let c_next = meta.query_advice(c, Rotation::next());
            let sum_next = meta.query_advice(sum, Rotation::cur());
            let r_next = meta.query_advice(r, Rotation::next());
            let shift_next = meta.query_advice(shift, Rotation::next());

            let v = c_cur - c_next * to_expr(4);
            vec![
              sum_next - out_cur.clone() - sum_cur,
              s.clone() * (shift_next - shift_cur - to_expr(1)), // inc the shift amout
              s * (r_cur - v)          // restrict the remainder
            ]
        });
        */

        ShortMultConfig {
            c,
            r,
            shift,
            out,
            sum,
            sel,
        }
    }

    fn assign_region(
        &self,
        input: Number<F>,
        layouter: &mut impl Layouter<F>,
        low: bool, // high 128 bits or low 128 bits
        num_chunks: usize,
        shift_base: F,
    ) -> Result<Number<F>, Error> {
        let config = self.config();
        let mut v = input.clone();
        layouter.assign_region(
            || "load private",
            |mut region| {
                for idx in 0..num_chunks {
                    config.sel.enable(&mut region, idx)?;
                }
                let mut r = v.clone().value.unwrap();
                let chunks:Vec<u64> = decompose_tweleve_bits::<F>(r, num_chunks);
                let two_pow_k_inv = F::from_u64(4 as u64).invert().unwrap();
                let mut shift = shift_base;
                let mut sum:F = F::zero();

                // assign c_0 and sum_0 as initial rows
                // | c_0 | remainder      | shift      | output | sum_0

                region.assign_advice (
                  || format!("r_{:?}", 0),
                  config.c,
                  0,
                  || Ok(v.clone().value.unwrap())
                )?;

                region.assign_advice (
                  || format!("r_{:?}", 0),
                  config.sum[0],
                  0,
                  || Ok(F::zero())
                )?;

                for (p, chunk) in chunks.iter().enumerate() {
                    let chunk_fp = F::from_u64(u64::try_from(*chunk).unwrap());
                    let chunk_next = (r - chunk_fp) * two_pow_k_inv;
                    let lookup = get_shift_lookup(chunk_fp, shift);
                    sum = sum + lookup;

                    // set the remainder at position p
                    region.assign_advice (
                      || format!("r_{:?}", p),
                      config.r,
                      p,
                      || Ok(chunk_fp)
                    )?;

                    // set the shift at position p
                    region.assign_advice (
                      || format!("s_{:?}", p),
                      config.shift,
                      p,
                      || Ok(shift)
                    )?;

                    // set the out at position p
                    region.assign_advice (
                      || format!("s_{:?}", p),
                      config.out[0],
                      p,
                      || Ok(lookup)
                    )?;

                    // set the next chunk
                    region.assign_advice (
                      || format!("c_{:?}", p + 1),
                      config.c,
                      p + 1,
                      || Ok(chunk_next)
                    )?;

                    // set the out at position p
                    let sum = region.assign_advice (
                      || format!("sum_{:?}", p+1),
                      config.sum[0],
                      p+1,
                      || Ok(sum)
                    )?;
                    r = chunk_next;
                    shift = shift + F::one();
                    v = Number::<F>{cell: sum, value: Some(chunk_next)}
                };
                Ok(())
            },
        )?;
        Ok(v)
    }
}

impl<F: FieldExt + PrimeFieldBits> Chip<F> for ShortMultChip<F> {
    type Config = ShortMultConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: FieldExt + PrimeFieldBits> ShortMult<F> for ShortMultChip<F> {
    fn mult(
        &self,
        mut layouter: impl Layouter<F>,
        a: Number<F>,
        b: Number<F>,
    ) -> Result<Number<F>, Error> {
        let out = None;
        Ok(out.unwrap())
    }
}
