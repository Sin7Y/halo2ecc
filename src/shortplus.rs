extern crate halo2;

use std::marker::PhantomData;
use crate::types::Number;

use halo2::{
    arithmetic::FieldExt,
    circuit::{Cell, Chip, Layouter, Region, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Instance, Selector},
    poly::Rotation,
};

trait ShortPlus <F: FieldExt>: Chip<F> {
    /// Variable representing a number.
    type Num;

    fn perform(
        &self,
        layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error>;
}

struct ShortPlusChip<F: FieldExt> {
    config: ShortPlusConfig,
    _marker: PhantomData<F>,
}

#[derive(Clone, Debug)]
struct ShortPlusConfig {
    /// Two fp numbers, three Columns each
    advice: [Column<Advice>; 2],
    carry: Column<Instance>,
    sel: Selector,
}

impl<F: FieldExt> ShortPlusChip<F> {
    fn construct(config: <Self as Chip<F>>::Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
    ) -> <Self as Chip<F>>::Config {
        let advice = [
          meta.advice_column(),
          meta.advice_column(),
        ];
        let carry = meta.instance_column();
        let sel = meta.selector();
        ShortPlusConfig {
            advice,
            carry,
            sel,
        }
    }
}

impl<F: FieldExt> Chip<F> for ShortPlusChip<F> {
    type Config = ShortPlusConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: FieldExt> ShortPlus<F> for ShortPlusChip<F> {
    type Num = Number<F>;

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
