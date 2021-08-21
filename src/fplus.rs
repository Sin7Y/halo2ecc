use halo2::{
    arithmetic::FieldExt,
    circuit::{Chip, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Instance, Selector},
};

use std::marker::PhantomData;
use crate::types::FieldNum;

trait FPlus <F: FieldExt>: Chip<F> {
    /// Variable representing a number.
    type Num;

    fn perform (
        &self,
        layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error>;
}

struct FPlusChip<F: FieldExt> {
    config: FPlusConfig,
    _marker: PhantomData<F>,
}

#[derive(Clone, Debug)]
struct FPlusConfig {
    /// Two fp numbers, three Columns each
    advice: [Column<Advice>; 6],
    instance: [Column<Instance>; 3],
    sel: Selector,
}

impl<F: FieldExt> FPlusChip<F> {
    fn construct(config: <Self as Chip<F>>::Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn create_gate(
        meta: &mut ConstraintSystem<F>,
    ) -> <Self as Chip<F>>::Config {
        let advice = [
          meta.advice_column(),
          meta.advice_column(),
          meta.advice_column(),
          meta.advice_column(),
          meta.advice_column(),
          meta.advice_column(),
        ];
        let instance = [
          meta.instance_column(),
          meta.instance_column(),
          meta.instance_column(),
        ];
        let sel = meta.selector();
        FPlusConfig {
            advice,
            instance,
            sel,
        }
    }
}

impl<F: FieldExt> Chip<F> for FPlusChip<F> {
    type Config = FPlusConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: FieldExt> FPlus<F> for FPlusChip<F> {
    type Num = FieldNum<F>;

    fn perform(
        &self,
        mut layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error> {
        let mut out = None;
        Ok(out.unwrap())
    }
}
