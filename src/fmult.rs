use halo2::{
    arithmetic::FieldExt,
    circuit::{Cell, Chip, Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Instance, Selector},
    poly::Rotation,
};

use crate::decompose::{DecomposeChip, DecomposeConfig};
use crate::plus::{PlusChip, Plus};
use crate::shortmult::{ShortMult, ShortMultChip};
use crate::types::{Fs, FsAdvice, Number};
use crate::utils::*;
use ff::PrimeFieldBits;
use std::marker::PhantomData;

trait FMult<Fp: FieldExt, F: FieldExt + PrimeFieldBits>: Chip<F> {
    fn mult(&self, layouter: &mut impl Layouter<F>, a: Fs<F>, b: Fs<F>) -> Result<Fs<F>, Error>;
}

struct FMultChip<Fp: FieldExt, F: FieldExt + PrimeFieldBits> {
    config: FMultConfig<F>,
    smult_chip: ShortMultChip<Fp, F>,
    decom_chip: DecomposeChip<F>,
    plus_chip: PlusChip<F>,
    _marker: PhantomData<F>,
}

#[derive(Clone, Debug)]
struct FMultConfig<F: FieldExt + PrimeFieldBits> {
    /// Two fp numbers, three Columns each
    x: FsAdvice<F>,
    y: FsAdvice<F>,
    z: FsAdvice<F>,
}

impl<Fp: FieldExt, F: FieldExt + PrimeFieldBits> FMultChip<Fp, F> {
    fn construct(
        config: <Self as Chip<F>>::Config,
        smult_chip: ShortMultChip<Fp, F>,
        decom_chip: DecomposeChip<F>,
        plus_chip: PlusChip<F>,
    ) -> Self {
        Self {
            config,
            smult_chip,
            decom_chip,
            plus_chip,
            _marker: PhantomData,
        }
    }

    fn create_base_gate(meta: &mut ConstraintSystem<F>) -> FMultConfig<F> {
        let x = FsAdvice::<F> {
            advices: [
                meta.advice_column(),
                meta.advice_column(),
                meta.advice_column(),
            ],
            _marker: PhantomData,
        };

        let y = FsAdvice::<F> {
            advices: [
                meta.advice_column(),
                meta.advice_column(),
                meta.advice_column(),
            ],
            _marker: PhantomData,
        };

        let z = FsAdvice::<F> {
            advices: [
                meta.advice_column(),
                meta.advice_column(),
                meta.advice_column(),
            ],
            _marker: PhantomData,
        };

        for i in 0..3 {
            meta.enable_equality(x.advices[i].into());
            meta.enable_equality(y.advices[i].into());
            meta.enable_equality(z.advices[i].into());
        }

        meta.create_gate("mult-split", |meta| {
            // Controlled by init_sel
            // | xl | xm | xh | yl | ym | yh | zl | zm | zh

            let xh = meta.query_advice(x.advices[2], Rotation::cur());
            let xm = meta.query_advice(x.advices[1], Rotation::cur());
            let xl = meta.query_advice(x.advices[0], Rotation::cur());
            let yh = meta.query_advice(y.advices[2], Rotation::cur());
            let ym = meta.query_advice(y.advices[1], Rotation::cur());
            let yl = meta.query_advice(y.advices[0], Rotation::cur());
            let zh = meta.query_advice(z.advices[2], Rotation::cur());
            let zm = meta.query_advice(z.advices[1], Rotation::cur());
            let zl = meta.query_advice(z.advices[0], Rotation::cur());

            let shift_80 = Expression::Constant(pow2::<F>(80));
            let shift_160 = Expression::Constant(pow2::<F>(160));

            vec![
                zl - (xl.clone() * yl.clone()
                    + (xm.clone() * yl.clone() + xl.clone() * ym.clone()) * shift_80
                    + xm.clone() * ym.clone() * shift_160),
                zm - (xm.clone() * yh.clone() + xh.clone() * ym.clone()),
                zh - (xh.clone() * yh.clone()),
            ]
        });

        return FMultConfig { x, y, z };
    }

    fn assign_fs(
        &self,
        region: &mut Region<F>,
        a: FsAdvice<F>,
        o: [F; 3],
        row_offset: usize,
        hint: &str,
    ) -> Fs<F> {
        let mut cells = [None, None, None];

        for i in 0..3 {
            let cell = region
                .assign_advice(
                    || format!("{}_{}", hint, i),
                    a.advices[i],
                    row_offset,
                    || Ok(o[i]),
                )
                .unwrap();
            cells[i] = Some(Number::<F> {
                cell,
                value: Some(o[0]),
            });
        }

        Fs::<F> {
            values: [cells[0].unwrap(), cells[1].unwrap(), cells[2].unwrap()],
        }
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

impl<Fp: FieldExt, F: FieldExt + PrimeFieldBits> FMultChip<Fp, F> {
    fn l1mult(&self, layouter: &mut impl Layouter<F>, a: Fs<F>, b: Fs<F>) -> Result<Fs<F>, Error> {
        let config = self.config();
        let mut output = None;

        layouter.assign_region(
            || "load private",
            |mut region| {
                let xh = a.clone().values[2].value.unwrap();
                let xm = a.clone().values[1].value.unwrap();
                let xl = a.clone().values[0].value.unwrap();

                let yh = b.clone().values[2].value.unwrap();
                let ym = b.clone().values[1].value.unwrap();
                let yl = b.clone().values[0].value.unwrap();

                let shift_80 = pow2::<F>(80);
                let shift_160 = pow2::<F>(160);

                let zh = xh.clone() * yh.clone();
                let zm = xh * ym.clone() + xm.clone() * yh;
                let zl = xl.clone() * yl.clone()
                    + xm.clone() * ym.clone() * shift_160
                    + (xl * ym + xm * yl) * shift_80;

                let _ = self.assign_fs(&mut region, config.x, [xl, xm, xh], 0, "fmult-x");
                let _ = self.assign_fs(&mut region, config.y, [yl, ym, yh], 0, "fmult-y");
                let z_fs = self.assign_fs(&mut region, config.z, [zl, zm, zh], 0, "fmult-z");

                output = Some(z_fs);

                Ok(())
            },
        )?;

        return Ok(output.unwrap());
    }
}

impl<Fp: FieldExt, F: FieldExt + PrimeFieldBits> FMult<Fp, F> for FMultChip<Fp, F> {
    fn mult(&self, layouter: &mut impl Layouter<F>, a: Fs<F>, b: Fs<F>) -> Result<Fs<F>, Error> {
        let l1output = self.l1mult(layouter, a, b)?;
        let (l, rem) = self
            .decom_chip
            .decompose(layouter, l1output.values[0], 10)?;
        let (m, h) = self.decom_chip.decompose(layouter, rem, 10)?;

        let (l2output, rem) = self.smult_chip.constrain(
            layouter,
            l1output.values[1],
            Fs { values: [l, m, h] },
            10,
            0,
        )?;

        let rem = self.plus_chip.plus(layouter, rem, l1output.values[2])?;
        let (l3output, rem) = self.smult_chip.constrain(
            layouter,
            rem,
            l2output,
            24,
            10,
        )?;

        // TODO: please apply normalize on l3output

        Ok(l1output)
    }
}
