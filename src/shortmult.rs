extern crate halo2;

use std::marker::PhantomData;
use crate::types::Number;
use std::convert::TryFrom;

use halo2::{
    arithmetic::FieldExt,
    circuit::{Cell, Chip, Layouter, Region, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance, TableColumn, Selector},
    poly::Rotation,
};

// Short Multiplication for a * b \in [2 ^ (16 * d) .. 2 ^ (16 * c)]
// let c = a * b then after decompose c into 16 bits as [x_i] we need to lookup table to
// calculate x_i' and then sum x_i to get the final result

#[derive(Clone, Debug)]
struct ShortMultConfig {
    decompose: Column<Advice>,
    shift: Column<Advice>,
    out: Column<Advice>,
    sel: Selector,
}

trait ShortMult <F: FieldExt>: Chip<F> {
    fn mult (
        &self,
        layouter: impl Layouter<F>,
        a: Number<F>,
        b: Number<F>,
    ) -> Result<Number<F>, Error>;
}

struct ShortMultChip<F: FieldExt> {
    config: ShortMultConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> ShortMultChip<F> {
    fn construct(config: <Self as Chip<F>>::Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        lookup_v: TableColumn,
    ) -> <Self as Chip<F>>::Config {
        let decompose = meta.advice_column();
        let shift = meta.advice_column();
        let out = meta.advice_column();
        let sel = meta.selector();
        ShortMultConfig {
            decompose,
            shift,
            out,
            sel,
        }
    }

    fn assign_region(
        &self,
        layouter: &mut impl Layouter<F>,
        low: bool, // high 128 bits or low 128 bits
        chunk_size: usize,
        shift_start: usize,
    ) -> Result<(), Error> {
        let pend = F::from(0);
        let config = self.config();
        layouter.assign_region(
            || "load private",
            |mut region| {
                for p in 0 .. chunk_size {
                    let s:u64 = if p < shift_start { 0 } else {
                        u64::try_from((p - shift_start)).unwrap()
                    };
                    let decompose_cell = region.assign_advice(
                        || format!("d_{}", p),
                        config.decompose,
                        p,
                        || Ok(pend),
                    )?;
                    let shift = region.assign_advice(
                        || format!("operand_{}", p),
                        config.shift,
                        p,
                        || Ok(F::from_u64(s)),
                    )?;
                    //region.constrain_equal(e.cell, cell)?;
                    //sum = sum + e.value.unwrap();
                    // missing selector enabling
                }
                Ok(())
            },
        )?;
        Ok(())
    }
}

impl<F: FieldExt> Chip<F> for ShortMultChip<F> {
    type Config = ShortMultConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: FieldExt> ShortMult<F> for ShortMultChip<F> {
    fn mult(
        &self,
        mut layouter: impl Layouter<F>,
        a: Number<F>,
        b: Number<F>,
    ) -> Result<Number<F>, Error> {
        let mut out = None;
        Ok(out.unwrap())
    }
}
