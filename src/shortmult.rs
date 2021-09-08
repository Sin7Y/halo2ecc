extern crate halo2;

use crate::types::{Fs, Number};
use crate::utils::*;
use ff::PrimeFieldBits;
use std::convert::TryFrom;
use std::convert::TryInto;
use std::marker::PhantomData;

use crate::byteoptable::{ShiftOpChip};

use halo2::{
    arithmetic::FieldExt,
    circuit::{Chip, Layouter},
    plonk::{
        Advice, Column, ConstraintSystem, Error, Expression, Selector,
        TableColumn,
    },
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
        layouter: &mut impl Layouter<F>,
        a: Number<F>,
        num_chunks: usize,
        shift_base: u64,
    ) -> Result<(Fs<F>, Number<F>), Error>;
}

pub struct ShortMultChip<Fp: FieldExt, F: FieldExt + PrimeFieldBits> {
    config: ShortMultConfig,
    shift_chip: ShiftOpChip<F>,
    _marker: PhantomData<F>,
    __marker: PhantomData<Fp>,
}

impl<Fp: FieldExt, F: FieldExt + PrimeFieldBits> ShortMultChip<Fp, F> {
    fn construct(config: <Self as Chip<F>>::Config, shift_chip: ShiftOpChip<F>) -> Self {
        Self {
            config,
            shift_chip,
            _marker: PhantomData,
            __marker: PhantomData,
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
        for i in 0..3 {
            cs.lookup(|meta| {
                let r_cur = meta.query_advice(r, Rotation::cur());
                let shift_cur = meta.query_advice(shift, Rotation::cur());
                let lookup_cur = meta.query_advice(lookup[i], Rotation::cur());
                vec![
                    (r_cur, lookup_v),
                    (shift_cur, lookup_s),
                    (lookup_cur, lookup_o),
                    (to_expr(u64::try_from(i).unwrap()), lookup_i),
                ]
            });
        }

        cs.create_gate("range check", |meta| {
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

            let sum_cur: [Expression<F>; 3] = sum
                .clone()
                .iter()
                .map(|sum| meta.query_advice(*sum, Rotation::cur()))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap();
            let sum_next: [Expression<F>; 3] = sum
                .iter()
                .map(|sum| meta.query_advice(*sum, Rotation::cur()))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap();

            let lookup_cur: [Expression<F>; 3] = lookup
                .iter()
                .map(|lookup| meta.query_advice(*lookup, Rotation::cur()))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap();

            let shift_cur = meta.query_advice(shift, Rotation::cur());
            let shift_next = meta.query_advice(shift, Rotation::next());

            vec![
                s.clone() * (sum_next[0].clone() - lookup_cur[0].clone() - sum_cur[0].clone()),
                s.clone() * (sum_next[1].clone() - lookup_cur[1].clone() - sum_cur[1].clone()),
                s.clone() * (sum_next[2].clone() - lookup_cur[2].clone() - sum_cur[2].clone()),
                s.clone() * (shift_next - shift_cur - to_expr(1)), // inc the shift amount
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
        layouter: &mut impl Layouter<F>,
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
            || "load private",
            |mut region| {
                for row in 0..num_chunks {
                    config.sel.enable(&mut region, row)?;

                    let s = region.assign_advice(
                        || format!("shift_{:?}", row),
                        config.shift,
                        row,
                        || Ok(F::from_u64(shift_base) + F::one()),
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

                    let c_cell = region.assign_advice(|| format!("c_{:?}", 0), config.c, 0, || Ok(c))?;
                    if row == 0 {
                        region.constrain_equal(input.cell, c_cell)?;
                    }

                    region.assign_advice(|| format!("rem_{:?}", row), config.r, row, || Ok(_rem))?;

                    for i in 0..3 {
                        let lookupi: F = projF(lookup, i);
                        region.assign_advice(
                            || format!("lookup_{:?}_{:?}", i, row),
                            config.lookup[i],
                            row,
                            || Ok(lookupi),
                        )?;

                        region.assign_advice(
                            || format!("sum_{:?}_{:?}", i, row),
                            config.r,
                            row,
                            || Ok(sum[i]),
                        )?;

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

                for i in 0..3 {
                    final_sum[i].cell = region.assign_advice(
                        || format!("sum_{:?}_{:?}", i, num_chunks),
                        config.r,
                        num_chunks,
                        || Ok(sum[i]),
                    )?;

                    final_sum[i].value = Some(sum[i]);
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
        layouter: &mut impl Layouter<F>,
        a: Number<F>,
        num_chunks: usize,
        shift_base: u64,
    ) -> Result<(Fs<F>, Number<F>), Error> {
        self.assign_region(layouter, a, num_chunks, shift_base)
    }
}
