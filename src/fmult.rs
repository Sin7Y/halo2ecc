use halo2::{
    arithmetic::FieldExt,
    circuit::{Chip, Layouter, Region, Cell},
    plonk::{
        Advice, Column, ConstraintSystem,
        Error, Instance,
        Selector, Expression
    },
    poly::Rotation,
};

use std::marker::PhantomData;
use crate::types::{Fs, FsAdvice, Number};
use crate::utils::*;
use crate::shortmult::{ShortMultChip, ShortMult};
use ff::PrimeFieldBits;

trait FMult <Fp: FieldExt, F: FieldExt + PrimeFieldBits>: Chip<F> {
    fn mult (
        &self,
        layouter: &mut impl Layouter<F>,
        a: Fs<F>,
        b: Fs<F>,
    ) -> Result<Fs<F>, Error>;
}

struct FMultChip<Fp: FieldExt, F: FieldExt + PrimeFieldBits> {
    config: FMultConfig<F>,
    shift_chip: ShortMultChip<Fp, F>,
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

impl<Fp: FieldExt, F: FieldExt + PrimeFieldBits> FMultChip<Fp, F> {
    fn construct(config: <Self as Chip<F>>::Config, shift_chip:ShortMultChip<Fp, F>) -> Self {
        Self {
            config,
            shift_chip,
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

    fn assign_fs(&self,
        region: &mut Region<F>,
        a: FsAdvice<F>,
        o: [F;3],
        row_offset:usize,
        hint:&str) -> Fs<F> {
        let cell0 = region.assign_advice(
            || format!("{}_{}", hint, 0),
            a.advices[0],
            row_offset,
            || Ok(o[0]),
        ).unwrap();
        let cell1 = region.assign_advice(
            || format!("{}_{}", hint, 1),
            a.advices[1],
            row_offset,
            || Ok(o[1]),
        ).unwrap();
        let cell2 = region.assign_advice(
            || format!("{}_{}", hint, 2),
            a.advices[2],
            row_offset,
            || Ok(o[2]),
        ).unwrap();
        Fs::<F> {values: [
                Number::<F>{cell:cell0, value:Some(o[0])},
                Number::<F>{cell:cell1, value:Some(o[1])},
                Number::<F>{cell:cell2, value:Some(o[2])},
        ]}
    }
}

impl<Fp: FieldExt, F: FieldExt + PrimeFieldBits> Chip<F> for FMultChip<Fp, F> {
    type Config = FMultConfig<F>;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<Fp: FieldExt, F: FieldExt + PrimeFieldBits> FMult<Fp, F> for FMultChip<Fp, F> {
    fn mult(
        &self,
        layouter: &mut impl Layouter<F>,
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

        // can skip Fr to Fp since it does not overflow
        let ch_s = [projF(ch, 0), F::zero(), F::zero()];
        let cm_s = [F::zero(), F::zero(), F::zero()];
        let cl_s = [F::zero(), F::zero(), F::zero()];

        let o = [ch_s[0] + cm_s[0] + cl_s[0],
                 ch_s[1] + cm_s[1] + cl_s[1],
                 ch_s[2] + cm_s[2] + cl_s[2]];

        let mut cl_num = None;
        let mut cm_num = None;
        let mut ch_num = None;

        let mut cl_repr = None;
        let mut cm_repr = None;
        let mut ch_repr = None;

        layouter.assign_region(
            || "load private",
            |mut region| {
                let cl_cell = region.assign_advice(
                    || format!("c_{}", 0),
                    config.x.advices[0],
                    1,
                    || Ok(cl),
                )?;
                cl_num = Some (Number::<F> {cell: cl_cell, value:Some(cl)});
                let cm_cell = region.assign_advice(
                    || format!("c_{}", 1),
                    config.x.advices[1],
                    1,
                    || Ok(cm),
                )?;
                cm_num = Some (Number::<F> {cell: cm_cell, value:Some(cm)});
                let ch_cell = region.assign_advice(
                    || format!("c_{}", 2),
                    config.x.advices[2],
                    1,
                    || Ok(ch),
                )?;
                ch_num = Some (Number::<F> {cell: ch_cell, value:Some(ch)});

                // Bind ch,cm,cl with there shifted results
                cl_repr = Some (self.assign_fs(&mut region, config.x.clone(),
                    cl_s, 2, "cl"));
                cm_repr = Some (self.assign_fs(&mut region, config.y.clone(),
                    cm_s, 2, "cm"));
                ch_repr = Some (self.assign_fs(&mut region, config.x.clone(),
                    ch_s, 3, "ch"));


                for i in 0..2 {
                    region.assign_advice(
                        || format!("x_{}", i),
                        config.x.advices[i],
                        0,
                        || Ok(a.values[i].value.unwrap()),
                    )?;
                }
                for i in 0..2 {
                    region.assign_advice(
                        || format!("y_{}", i),
                        config.x.advices[i],
                        0,
                        || Ok(b.values[i].value.unwrap()),
                    )?;
                }
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
        // FIXME: the last argument is the shift starting index ?
        self.shift_chip.constrain(layouter,
            cm_num.unwrap(),
            cm_repr.unwrap(),
            (96 + 80)/8 + 1,
            F::from(0),
        );
        self.shift_chip.constrain(layouter,
            ch_num.unwrap(),
            ch_repr.unwrap(),
            (96 + 96)/8 + 1,
            F::from((320 - 240)/8),
        );
        Ok(out.unwrap())
    }
}
