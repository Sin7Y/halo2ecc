extern crate halo2;

use std::marker::PhantomData;
use std::convert::TryInto;
use crate::types::{Number, Fs};
use crate::utils::*;
use crate::decompose::*;
use std::convert::TryFrom;
use ff::{PrimeFieldBits};

use halo2::{
    arithmetic::FieldExt,
    circuit::{Cell, Chip, Layouter, Region, SimpleFloorPlanner},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem,
        Error, Instance, TableColumn, Selector,
        Expression
    },
    poly::Rotation,
};

// Suppose that c = a * 2^256. Then it follows that
// after decompose c into 8 bits as [x_i]
// we need to lookup our shift multiplication table to
// calculate x_i' and then sum x_i to get the final result

#[derive(Clone, Debug)]
struct ShortMultConfig {
    c: Column<Advice>,
    r: Column<Advice>,
    shift: Column<Advice>,
    lookup: [Column<Advice>;3],
    sum: [Column<Advice>;3],
    sel: Selector,
}

trait ShortMult <F: FieldExt + PrimeFieldBits>: Chip<F> {
    fn mult (
        &self,
        layouter: &mut impl Layouter<F>,
        a: Number<F>,
        num_chunks: usize,
        shift_base: F,
    ) -> Result<Fs<F>, Error>;
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
        let lookup = [cs.advice_column(), cs.advice_column(), cs.advice_column()];
        let sum = [cs.advice_column(), cs.advice_column(), cs.advice_column()];
        let sel = cs.selector();

        // Using lookup has side benifits which ensures that
        // remainder does not overflow so that it
        // equals performing a range check of each remainder
        for i in 0 .. 2 {
          cs.lookup(|meta| {
            let r_cur = meta.query_advice(r, Rotation::cur());
            let shift_cur = meta.query_advice(shift, Rotation::cur());
            let lookup_cur = meta.query_advice(lookup[i], Rotation::cur());
            vec![(r_cur, lookup_v), (shift_cur, lookup_s),
                 (lookup_cur, lookup_o), (to_expr(u64::try_from(i).unwrap()), lookup_i)]
          });
        }

        cs.create_gate("range check", |meta| {
            //
            // | c_cur   | remainder      | shift      | lookup_{0,1,2} | sum_{0,1,2}
            // | c_next  | remainder_next | shift_next | lookup_{0,1,2} | ..........
            // .....
            // | c_final | <- should be zero           |                | sum_{0,1,2}
            //
            let s = meta.query_selector(sel);
            let c_cur = meta.query_advice(c, Rotation::cur());
            let sum_cur:[Expression<F>;3]
                 = sum.clone().iter()
                    .map(|sum| meta.query_advice(*sum, Rotation::cur()))
                    .collect::<Vec<_>>().try_into().unwrap();
            let lookup_cur:[Expression<F>;3]
                 = lookup.iter()
                    .map(|lookup| meta.query_advice(*lookup, Rotation::cur()))
                    .collect::<Vec<_>>().try_into().unwrap();
            let r_cur = meta.query_advice(r, Rotation::cur());
            let shift_cur = meta.query_advice(shift, Rotation::cur());

            let c_next = meta.query_advice(c, Rotation::next());
            let sum_next:[Expression<F>;3] = sum.iter()
                            .map(|sum| meta.query_advice(*sum, Rotation::cur()))
                             .collect::<Vec<_>>().try_into().unwrap();
            let r_next = meta.query_advice(r, Rotation::next());
            let shift_next = meta.query_advice(shift, Rotation::next());

            let v = c_cur - c_next * to_expr(256);
            vec![
              sum_next[0].clone() - lookup_cur.clone()[0].clone() - sum_cur[0].clone(),
              s.clone() * (shift_next - shift_cur - to_expr(1)), // inc the shift amout
              s * (r_cur - v)          // restrict the remainder
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
        layouter: &mut impl Layouter<F>,
        input: Number<F>,
        num_chunks: usize,
        shift_base: F,
    ) -> Result<Fs<F>, Error> {
        let config = self.config();
        let mut v = [input.clone(), input.clone(), input.clone()];
        layouter.assign_region(
            || "load private",
            |mut region| {
                for idx in 0..num_chunks {
                    config.sel.enable(&mut region, idx)?;
                }
                let mut r = input.clone().value.unwrap();
                let chunks:Vec<u64> = decompose_tweleve_bits::<F>(r, num_chunks);
                let two_pow_k_inv = F::from_u64(4 as u64).invert().unwrap();
                let mut shift = shift_base;
                let mut sum = [F::zero(), F::zero(), F::zero()];

                // assign c_0 and sum_0 as initial rows
                // | c_0 | remainder | shift  | lookup_{0,1,2} | sum_{0,1,2}

                region.assign_advice (
                  || format!("c_{:?}", 0),
                  config.c,
                  0,
                  || Ok(input.clone().value.unwrap())
                )?;

                // The first row of sum are all zero
                for i in 0..2 {
                  region.assign_advice (
                    || format!("sum_{:?}_{:?}", i, 0),
                    config.sum[i],
                    0,
                    || Ok(F::zero())
                  )?;
                }

                for (p, chunk) in chunks.iter().enumerate() {
                    let chunk_fp = F::from_u64(u64::try_from(*chunk).unwrap());
                    let chunk_next = (r - chunk_fp) * two_pow_k_inv;
                    let lookup = [
                      get_shift_lookup(chunk_fp, shift,0),
                      get_shift_lookup(chunk_fp, shift,1),
                      get_shift_lookup(chunk_fp, shift,1),
                    ];
                    for i in 0..2 {
                        sum[i] = sum[i] + lookup[i];
                        // set the out at position p
                        region.assign_advice (
                          || format!("s_{:?}", p),
                          config.lookup[0],
                          p,
                          || Ok(lookup[i])
                        )?;
                        let s = region.assign_advice (
                          || format!("sum_{:?}", p+1),
                          config.sum[i],
                          p+1,
                          || Ok(sum[i])
                        )?;
                        v[i] = Number::<F>{cell: s, value: Some(sum[i])}
                    };

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


                    // set the next chunk
                    region.assign_advice (
                      || format!("c_{:?}", p + 1),
                      config.c,
                      p + 1,
                      || Ok(chunk_next)
                    )?;

                    // set the out at position p
                    r = chunk_next;
                    shift = shift + F::one();
                };
                Ok(())
            },
        )?;
        Ok(Fs::<F> {values: v})
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
        layouter: &mut impl Layouter<F>,
        a: Number<F>,
        num_chunks: usize,
        shift_base: F,
    ) -> Result<Fs<F>, Error> {
        self.assign_region(layouter, a, num_chunks, shift_base)
    }
}
