use halo2::{
    arithmetic::FieldExt,
    circuit::{Chip, Layouter},
    plonk::{
        Advice, Column, ConstraintSystem,
        Error, Selector
    },
    poly::Rotation,
};

use std::marker::PhantomData;
use crate::types::{Number};
use crate::utils::*;
use crate::decompose::{DecomposeChip};

pub trait RangeCheck <F: FieldExt>: Chip<F> {
    fn range_check (
        &self,
        layouter: &mut impl Layouter<F>,
        x: Number<F>,
        csize: usize,
    ) -> Result<(), Error>;
}

pub struct RangeCheckChip<F: FieldExt> {
    config: RangeCheckConfig,
    decompose_chip: DecomposeChip<F>,
}

#[derive(Clone, Debug)]
pub struct RangeCheckConfig {
    /// Two fp numbers, three Columns each
    carry: Column<Advice>,
    remainder: Column<Advice>,
    sel: Selector,
}

impl<F: FieldExt> RangeCheckChip<F> {
    pub fn construct(config: <Self as Chip<F>>::Config, decompose_chip:DecomposeChip<F>) -> Self {
        Self {
            config,
            decompose_chip,
        }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
    ) -> <Self as Chip<F>>::Config {
        let carry = meta.advice_column();
        let remainder = meta.advice_column();

        meta.enable_equality(carry.into());
        meta.enable_equality(remainder.into());

        let sel = meta.selector();

        meta.create_gate("range-check-gate", |meta| {
            let s = meta.query_selector(sel);

            // pure sum and carry arithment
            // | carry |  remainder |
            let carry_cur = meta.query_advice(carry, Rotation::cur());
            vec![ s * carry_cur ]
        });

        RangeCheckConfig {
            carry,
            remainder,
            sel,
        }
    }
}

impl<F: FieldExt> Chip<F> for RangeCheckChip<F> {
    type Config = RangeCheckConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: FieldExt> RangeCheck<F> for RangeCheckChip<F> {
    fn range_check(
        &self,
        layouter: &mut impl Layouter<F>,
        x: Number<F>,
        csize: usize,
    ) -> Result<(), Error> {
        let config = self.config();

        let mut carry_cell = None;
        let mut remainder_cell = None;

        layouter.assign_region(
            || "range_check",
            |mut region| {
                config.sel.enable(&mut region, 0)?;
                carry_cell = Some( region.assign_advice(
                    || format!("carry"),
                    config.carry,
                    0,
                    || Ok(F::zero()),
                )?);

                remainder_cell = Some (region.assign_advice(
                    || format!("remainder"),
                    config.remainder,
                    0,
                    || Ok(proj_f::<F, F>(x.value.unwrap(), csize * 8)),
                )?);
                Ok(())
            },
        )?;

        let (sum_l, carry_l) =
            self.decompose_chip.decompose(layouter, x, csize)?;
        layouter.assign_region(
            || "constraint_equal",
            |mut region| {
                // FIXME: Shall we allow constrain for remainder ?
                //region.constrain_equal(remainder_cell.unwrap(), sum_l.cell)?;
                region.constrain_equal(carry_cell.unwrap(), carry_l.cell)?;
                Ok(())
            },
        )?;
        Ok(())
    }
}

use halo2::pasta::{Fp};
use crate::testchip::*;
use crate::decompose::*;
use halo2::plonk::Circuit;
use halo2::circuit::SimpleFloorPlanner;

#[derive(Clone, Default)]
struct MyCircuit {
    x0: Fp,
}

#[derive(Clone, Debug)]
struct TestCircConfig {
    rconfig: RangeCheckConfig,
    dconfig: DecomposeConfig<Fp>,
    tconfig: TestConfig,
}

impl Circuit<Fp> for MyCircuit {
    type Config = TestCircConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(cs: &mut ConstraintSystem<Fp>) -> Self::Config {
        let table_col = cs.lookup_table_column();
        TestCircConfig {
            rconfig: RangeCheckChip::<Fp>::configure(cs),
            dconfig: DecomposeChip::<Fp>::configure(cs, table_col),
            tconfig: TestChip::<Fp>::configure(cs),
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fp>,
    ) -> Result<(), Error> {
        println!("Start synthesize ...");
        let test_chip = TestChip::<Fp>::construct(config.tconfig);
        let c0 = test_chip.load_private(layouter.namespace(|| "cell"), Some(self.x0))?;
        let x0 = Number::<Fp>{cell:c0.cell, value:Some(self.x0)};
        let dchip = DecomposeChip::<Fp>::constructor(config.dconfig);
        dchip.load_range_table(&mut layouter)?;
        let rchip = RangeCheckChip::<Fp>::construct(config.rconfig, dchip);
        rchip.range_check(&mut layouter, x0, 10);
        Ok(())
    }
}

#[test]
fn range_check_test() {
    use halo2::dev::MockProver;
    let pub_inputs = vec![];

    let circuit = MyCircuit {
        x0: Fp::from(0x1),
    };
    let prover = MockProver::run(10, &circuit, vec![pub_inputs]).unwrap();
    let presult = prover.verify();
    println!("Error {:?}", presult);

    assert!(presult.is_ok());
}
