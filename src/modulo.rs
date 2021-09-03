extern crate halo2;

use std::marker::PhantomData;

use halo2::{
    arithmetic::FieldExt,
    circuit::{Cell, Chip, Layouter, Region, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Instance, Selector},
    poly::Rotation,
};

struct ModuloChip<F: FieldExt> {
    config: ModuloConfig,
    _marker: PhantomData<F>,
}

struct ModuloConfig {
    /// Two fp numbers, three Columns each
    advice: [Column<Advice>; 6],
    instance: [Column<Instance>; 3],
    sel: Selector,
}

impl<F: FieldExt> ModuloConfig<F> {
    fn construct(config: <Self as Chip<F>>::Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
    ) -> <Self as Chip<F>>::Config {
        let advice =
        FieldConfig {
            advice,
            instance,
            s_mul,
            constant,
        }
    }
}

impl<F: FieldExt> Chip<F> for ModuloChip<F> {
    type Config = FieldConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: FieldExt> BinaryChip<F> for BinaryChip<F> {

    type Num = FieldNum<F>;

    fn perform (
        &self,
        mut layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config();
        let mut out = None;
        Ok(out.unwrap())
    }

    fn expose (
        &self,
        mut layouter: impl Layouter<F>,
        num: Self::Num,
        row: usize,
    ) -> Result<(), Error> {
        let config = self.config();
        ()
        //layouter.constrain_instance(num.cell, config.instance, row)
    }
}

