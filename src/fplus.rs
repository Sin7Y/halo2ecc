use halo2::{
    arithmetic::FieldExt,
    circuit::{Chip, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Instance, Selector},
};

use std::marker::PhantomData;
use crate::types::{Fs, FsAdvice};
use ff::PrimeFieldBits;

trait FPlus <F: FieldExt + PrimeFieldBits>: Chip<F> {
    fn plus (
        &self,
        layouter: impl Layouter<F>,
        a: Fs<F>,
        b: Fs<F>,
    ) -> Result<FsAdvice<F>, Error>;
}

struct FPlusChip<F: FieldExt + PrimeFieldBits> {
    config: FPlusConfig<F>,
    _marker: PhantomData<F>,
}

#[derive(Clone, Debug)]
struct FPlusConfig<F: FieldExt + PrimeFieldBits> {
    /// Two fp numbers, three Columns each
    x: FsAdvice<F>,
    y: FsAdvice<F>,
    sel: Selector,
}

impl<F: FieldExt + PrimeFieldBits> FPlusChip<F> {
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

        let sel = meta.selector();
        FPlusConfig {
            x,
            y,
            sel,
        }
    }
}

impl<F: FieldExt + PrimeFieldBits> Chip<F> for FPlusChip<F> {
    type Config = FPlusConfig<F>;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: FieldExt + PrimeFieldBits> FPlus<F> for FPlusChip<F> {
    fn plus(
        &self,
        mut layouter: impl Layouter<F>,
        a: Fs<F>,
        b: Fs<F>,
    ) -> Result<FsAdvice<F>, Error> {
        let mut out = None;
        Ok(out.unwrap())
    }
}
