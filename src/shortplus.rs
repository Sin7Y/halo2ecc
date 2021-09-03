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
        inputs: Vec<Self::Num>,
    ) -> Result<Self::Num, Error>;

    fn expose_carry_remainder(
        &self,
        layouter: impl Layouter<F>,
        remainder: Self::Num,
    ) -> Result<(), Error>;


}

struct ShortPlusChip<F: FieldExt> {
    config: ShortPlusConfig,
    _marker: PhantomData<F>,
}

#[derive(Clone, Debug)]
struct ShortPlusConfig {
    /// Two fp numbers, three Columns each
    advice: Column<Advice>,
    carry: Column<Advice>,
    sel: Selector,
}

/// For non overflow sum of a sequence of short numbers we can simply calculate
/// the sum and produce a carry number plus a remainder
/// For example sum a_i = carry * 2^k + remainder
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
        let advice = meta.advice_column();
        let carry = meta.advice_column();
        let sum = meta.advice_column();
        let sel = meta.selector();
        let mut c = 0;

        meta.create_gate("sum", |meta| {
            let sum_k = meta.query_advice(sum, Rotation::cur());
            let operand = meta.query_advice(advice, Rotation::cur());
            let sum_kplus = meta.query_advice(sum, Rotation::next());
            let s_sum = meta.query_selector(sel);
            vec![s_sum * (sum_k + operand - sum_kplus)]
        });

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

    fn expose_carry_remainder(
        &self,
        mut layouter: impl Layouter<F>,
        remainder: Self::Num,
    ) -> Result<(), Error> {
        // the final sum = carry * 2^d + remainder
        Ok(())
    }

    fn perform(
        &self,
        mut layouter: impl Layouter<F>,
        inputs: Vec<Self::Num>,
    ) -> Result<Self::Num, Error> {
        let mut out = None;
        Ok(out.unwrap())
    }
}
