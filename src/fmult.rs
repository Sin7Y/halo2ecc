use halo2::{
    arithmetic::FieldExt,
    circuit::{Chip, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Instance, Selector, Expression},
    poly::Rotation,
};

use std::marker::PhantomData;
use crate::types::{Fs, FsAdvice, Number};
use crate::utils::*;
use ff::PrimeFieldBits;

trait FMult <F: FieldExt + PrimeFieldBits>: Chip<F> {
    fn mult (
        &self,
        layouter: impl Layouter<F>,
        a: Fs<F>,
        b: Fs<F>,
    ) -> Result<Fs<F>, Error>;
}

struct FMultChip<F: FieldExt + PrimeFieldBits> {
    config: FMultConfig<F>,
    _marker: PhantomData<F>,
}

#[derive(Clone, Debug)]
struct FMultConfig<F: FieldExt + PrimeFieldBits> {
    /// Two fp numbers, three Columns each
    x: FsAdvice<F>,
    y: FsAdvice<F>,
    isel: Selector,
    ssel: Selector,
}

impl<F: FieldExt + PrimeFieldBits> FMultChip<F> {
    fn construct(config: <Self as Chip<F>>::Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn create_gate(
        meta: &mut ConstraintSystem<F>,
    ) -> <Self as Chip<F>>::Config {
        let x = FsAdvice::<F> {advices: [
          meta.advice_column(),
          meta.advice_column(),
          meta.advice_column(),
        ], _marker: PhantomData};
        let y = FsAdvice::<F> {advices: [
          meta.advice_column(),
          meta.advice_column(),
          meta.advice_column(),
        ], _marker: PhantomData};

        for i in 0..2 {
            meta.enable_equality(x.advices[i].into());
            meta.enable_equality(y.advices[i].into());
        }

        let isel = meta.selector();
        let ssel = meta.selector();

        meta.create_gate("mult-split", |meta| {
            let init_sel = meta.query_selector(isel);
            let sum_sel  = meta.query_selector(ssel);

            // Controlled by init_sel
            // | xl | xm   | xh   | yh | ym | yl |
            // | v0 | v240 | v320 |


            // Controlled by sum_sel
            // | al | am   | ah   |  bl | bm | bh ---- cur
            // | cl | cm   | ch   |  ol | om | oh ---- next

            let xh = meta.query_advice(x.advices[2], Rotation::cur());
            let xm = meta.query_advice(x.advices[1], Rotation::cur());
            let xl = meta.query_advice(x.advices[0], Rotation::cur());

            let yh = meta.query_advice(y.advices[2], Rotation::cur());
            let ym = meta.query_advice(y.advices[1], Rotation::cur());
            let yl = meta.query_advice(y.advices[0], Rotation::cur());

            let v320 = meta.query_advice(x.advices[2], Rotation::next());
            let v240 = meta.query_advice(x.advices[1], Rotation::next());
            let v0 = meta.query_advice(x.advices[0], Rotation::next());
            let shift_80 = Expression::Constant(pow2::<F>(80));
            let shift_160 = Expression::Constant(pow2::<F>(160));

            let ah = meta.query_advice(x.advices[2], Rotation::cur());
            let am = meta.query_advice(x.advices[1], Rotation::cur());
            let al = meta.query_advice(x.advices[0], Rotation::cur());

            let bh = meta.query_advice(y.advices[2], Rotation::cur());
            let bm = meta.query_advice(y.advices[1], Rotation::cur());
            let bl = meta.query_advice(y.advices[0], Rotation::cur());

            let ch = meta.query_advice(x.advices[2], Rotation::next());
            let cm = meta.query_advice(x.advices[1], Rotation::next());
            let cl = meta.query_advice(x.advices[0], Rotation::next());

            let oh = meta.query_advice(x.advices[2], Rotation::next());
            let om = meta.query_advice(x.advices[1], Rotation::next());
            let ol = meta.query_advice(x.advices[0], Rotation::next());

            vec![
                init_sel.clone() * (v320 - xh.clone() * yh.clone()),
                init_sel.clone() * (v240 - (xh * ym.clone() + xm.clone() * yh)),
                init_sel * (v0 - (xl.clone() * yl.clone() + xm.clone()*ym.clone()*shift_160 + (xl*ym + xm * yl)*shift_80)),
                sum_sel.clone() * (oh - ch - ah - bh),
                sum_sel.clone() * (ol - cl - al - bl),
                sum_sel.clone() * (om - cm - am - bm),
            ]
        });

        FMultConfig {
            x,
            y,
            isel,
            ssel,
        }
    }
}

impl<F: FieldExt + PrimeFieldBits> Chip<F> for FMultChip<F> {
    type Config = FMultConfig<F>;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: FieldExt + PrimeFieldBits> FMult<F> for FMultChip<F> {
    fn mult(
        &self,
        mut layouter: impl Layouter<F>,
        a: Fs<F>,
        b: Fs<F>,
    ) -> Result<Fs<F>, Error> {
        let config = self.config();
        let mut out = None;
        let xh = a.clone().values[2].value.unwrap();
        let xm = a.clone().values[1].value.unwrap();
        let xl = a.clone().values[0].value.unwrap();

        let yh = b.clone().values[2].value.unwrap();
        let ym = b.clone().values[1].value.unwrap();
        let yl = b.clone().values[0].value.unwrap();


        let shift_80 = pow2::<F>(80);
        let shift_160 = pow2::<F>(160);

        let ch = xh.clone() * yh.clone();
        let cm = xh * ym.clone() + xm.clone() * yh;
        let cl = xl.clone() * yl.clone()
                 + xm.clone()*ym.clone()*shift_160
                 + (xl*ym + xm * yl)*shift_80;

        // Keep little end
        let ch_s = [F::zero(), F::zero(), F::zero()];
        let cm_s = [F::zero(), F::zero(), F::zero()];
        let cl_s = [F::zero(), F::zero(), F::zero()];

        let o = [ch_s[0] + cm_s[0] + cl_s[0],
                 ch_s[1] + cm_s[1] + cl_s[1],
                 ch_s[2] + cm_s[2] + cl_s[2]];

        layouter.assign_region(
            || "load private",
            |mut region| {
                for i in 0..2 {
                    region.assign_advice(
                        || format!("x_{}", i),
                        config.x.advices[i],
                        0,
                        || Ok(a.values[i].value.unwrap()),
                    )?;
                    region.assign_advice(
                        || format!("cl_{}", i),
                        config.x.advices[i],
                        2,
                        || Ok(cl_s[i]),
                    )?;
                    region.assign_advice(
                        || format!("ch_{}", i),
                        config.x.advices[i],
                        3,
                        || Ok(ch_s[i]),
                    )?;

                }
                for i in 0..2 {
                    region.assign_advice(
                        || format!("y_{}", i),
                        config.x.advices[i],
                        0,
                        || Ok(b.values[i].value.unwrap()),
                    )?;
                    region.assign_advice(
                        || format!("cm_{}", i),
                        config.y.advices[i],
                        2,
                        || Ok(cm_s[i]),
                    )?;
                }
                region.assign_advice(
                    || format!("c_{}", 0),
                    config.x.advices[0],
                    1,
                    || Ok(cl),
                )?;
                region.assign_advice(
                    || format!("c_{}", 1),
                    config.x.advices[1],
                    1,
                    || Ok(cm),
                )?;
                region.assign_advice(
                    || format!("c_{}", 2),
                    config.x.advices[2],
                    1,
                    || Ok(ch),
                )?;
                let cell0 = region.assign_advice(
                    || format!("o_{}", 0),
                    config.y.advices[0],
                    3,
                    || Ok(o[0]),
                )?;
                let cell1 = region.assign_advice(
                    || format!("o_{}", 1),
                    config.y.advices[1],
                    3,
                    || Ok(o[1]),
                )?;
                let cell2 = region.assign_advice(
                    || format!("o_{}", 2),
                    config.y.advices[2],
                    3,
                    || Ok(o[2]),
                )?;
                out = Some (Fs::<F> {values: [
                        Number::<F>{cell:cell0, value:Some(o[0])},
                        Number::<F>{cell:cell1, value:Some(o[1])},
                        Number::<F>{cell:cell2, value:Some(o[2])},
                      ]});
                Ok(())
            },
        );
        Ok(out.unwrap())
    }
}
