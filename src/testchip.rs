extern crate halo2;

use crate::types::Number;
use std::marker::PhantomData;

use halo2::{
    arithmetic::FieldExt,
    circuit::{Chip, Layouter, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Instance},
};

pub struct TestChip<F: FieldExt> {
    config: TestConfig,
    _marker: PhantomData<F>,
}

#[derive(Clone, Debug)]
pub struct TestConfig {
    advice: Column<Advice>,
    instance: Column<Instance>,
    constant: Column<Fixed>
}

pub trait TestChipTrait<F: FieldExt>: Chip<F> {
    fn load_private(&self, layouter: impl Layouter<F>, a: Option<F>) -> Result<Number<F>, Error>;
    fn load_constant(&self, layouter: impl Layouter<F>, constant: F) -> Result<Number<F>, Error>;
    fn expose_public(
        &self,
        layouter: impl Layouter<F>,
        num: Number<F>,
        row: usize,
    ) -> Result<(), Error>;
}

impl<F: FieldExt> TestChip<F> {
    pub fn construct(config: <Self as Chip<F>>::Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    /// Only one row is used to store all the test inputs

    pub fn configure(meta: &mut ConstraintSystem<F>) -> <Self as Chip<F>>::Config {
        let advice = meta.advice_column();
        let instance = meta.instance_column();
        let constant = meta.fixed_column();
        meta.enable_equality(instance.into());
        meta.enable_equality(advice.into());
        meta.enable_constant(constant);
        TestConfig { advice, instance, constant }
    }
}

impl<F: FieldExt> Chip<F> for TestChip<F> {
    type Config = TestConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: FieldExt> TestChipTrait<F> for TestChip<F> {
    fn load_private(
        &self,
        mut layouter: impl Layouter<F>,
        value: Option<F>,
    ) -> Result<Number<F>, Error> {
        let config = self.config();

        let mut num = None;
        layouter.assign_region(
            || "load private",
            |mut region| {
                let cell = region.assign_advice(
                    || "private input",
                    config.advice,
                    0,
                    || value.ok_or(Error::SynthesisError),
                )?;
                num = Some(Number { cell, value });
                Ok(())
            },
        )?;
        Ok(num.unwrap())
    }

    fn load_constant(
        &self,
        mut layouter: impl Layouter<F>,
        constant: F,
    ) -> Result<Number<F>, Error> {
        let config = self.config();

        let mut num = None;
        layouter.assign_region(
            || "load constant",
            |mut region| {
                let cell = region.assign_advice_from_constant(
                    || "constant value",
                    config.advice,
                    0,
                    constant,
                )?;
                num = Some(Number {
                    cell,
                    value: Some(constant),
                });
                Ok(())
            },
        )?;
        Ok(num.unwrap())
    }

    fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        num: Number<F>,
        row: usize,
    ) -> Result<(), Error> {
        let config = self.config();
        layouter.constrain_instance(num.cell, config.instance, row)
    }
}

#[derive(Default)]
struct MyCircuit<F: FieldExt> {
    a: Option<F>,
}

impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
    // Since we are using a single chip for everything, we can just reuse its config.
    type Config = TestConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        TestChip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let field_chip = TestChip::<F>::construct(config);
        let a = field_chip.load_private(layouter.namespace(|| "load a"), self.a)?; // cursor 0
        field_chip.expose_public(layouter.namespace(|| "expose c"), a, 0)
    }
}

#[test]
fn test() {
    use halo2::{dev::MockProver, pasta::Fp};

    // ANCHOR: test-circuit
    // The number of rows in our circuit cannot exceed 2^k. Since our example
    // circuit is very small, we can pick a very small value here.
    let k = 4;

    // Prepare the private and public inputs to the circuit!
    let a = Fp::from(2);
    let c = Fp::from(2);

    // Instantiate the circuit with the private inputs.
    let circuit = MyCircuit {
        a: Some(a),
    };

    let mut public_inputs = vec![c];

    // Given the correct public input, our circuit will verify.
    let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
    assert_eq!(prover.verify(), Ok(()));

    // If we try some other public input, the proof will fail!
    public_inputs[0] += Fp::one();
    let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();
    assert!(prover.verify().is_err());
}
