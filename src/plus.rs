use halo2::{
  arithmetic::FieldExt,
  circuit::{Chip, Layouter},
  plonk::{Advice, Column, ConstraintSystem, Error, Selector},
  poly::Rotation,
};

use crate::types::Number;
use ff::PrimeFieldBits;
use std::marker::PhantomData;

pub trait Plus<F: FieldExt + PrimeFieldBits>: Chip<F> {
  fn plus(
    &self,
    layouter: &mut impl Layouter<F>,
    a: Number<F>,
    b: Number<F>,
  ) -> Result<Number<F>, Error>;
}

pub struct PlusChip<F: FieldExt + PrimeFieldBits> {
  config: PlusConfig,
  _marker: PhantomData<F>,
}

#[derive(Clone, Debug)]
pub struct PlusConfig {
  x: Column<Advice>,
  y: Column<Advice>,
  z: Column<Advice>,
  sel: Selector,
}

impl<F: FieldExt + PrimeFieldBits> PlusChip<F> {
  pub fn construct(config: <Self as Chip<F>>::Config) -> Self {
    Self {
      config,
      _marker: PhantomData,
    }
  }

  pub fn configure(meta: &mut ConstraintSystem<F>) -> <Self as Chip<F>>::Config {
    let x = meta.advice_column();
    let y = meta.advice_column();
    let z = meta.advice_column();
    let sel = meta.selector();

    meta.enable_equality(x.into());
    meta.enable_equality(y.into());
    meta.enable_equality(z.into());

    meta.create_gate("add check", |meta| {
      let x_cur = meta.query_advice(x, Rotation::cur());
      let y_cur = meta.query_advice(y, Rotation::cur());
      let z_cur = meta.query_advice(z, Rotation::cur());
      let s = meta.query_selector(sel);

      vec![s * (z_cur - x_cur - y_cur)]
    });

    PlusConfig { x, y, z, sel }
  }
}

impl<F: FieldExt + PrimeFieldBits> Chip<F> for PlusChip<F> {
  type Config = PlusConfig;
  type Loaded = ();

  fn config(&self) -> &Self::Config {
    &self.config
  }

  fn loaded(&self) -> &Self::Loaded {
    &()
  }
}

impl<F: FieldExt + PrimeFieldBits> Plus<F> for PlusChip<F> {
  fn plus(
    &self,
    layouter: &mut impl Layouter<F>,
    x: Number<F>,
    y: Number<F>,
  ) -> Result<Number<F>, Error> {
    let config = self.config();
    let mut z = None;

    layouter.assign_region(
      || "plus",
      |mut region| {
        let x_value = x.value.unwrap();
        let y_value = y.value.unwrap();
        let z_value = x_value + y_value;

        config.sel.enable(&mut region, 0)?;

        let x_cell = region.assign_advice(|| format!("x"), config.x, 0, || Ok(x_value))?;
        let y_cell = region.assign_advice(|| format!("y"), config.y, 0, || Ok(y_value))?;
        region.constrain_equal(x.cell, x_cell)?;
        region.constrain_equal(y.cell, y_cell)?;

        let z_cell = region.assign_advice(|| format!("z"), config.z, 0, || Ok(z_value))?;

        println!("{:?} {:?} {:?}", x_value, y_value, z_value);

        z = Some(Number {
          cell: z_cell,
          value: Some(z_value),
        });

        Ok(())
      },
    )?;

    Ok(z.unwrap())
  }
}

#[derive(Default)]
struct MyCircuit<F: FieldExt + PrimeFieldBits> {
  x: Option<F>,
  y: Option<F>,
}

use crate::testchip::*;
use halo2::circuit::SimpleFloorPlanner;
use halo2::plonk::Circuit;

#[derive(Clone, Debug)]
pub struct CircuitConfig {
  plusc: PlusConfig,
  testc: TestConfig,
}

impl<F: FieldExt + PrimeFieldBits> Circuit<F> for MyCircuit<F> {
  // Since we are using a single chip for everything, we can just reuse its config.
  type Config = CircuitConfig;
  type FloorPlanner = SimpleFloorPlanner;

  fn without_witnesses(&self) -> Self {
    Self::default()
  }
  fn configure(cs: &mut ConstraintSystem<F>) -> Self::Config {
    let plusc = PlusChip::<F>::configure(cs);
    let testc = TestChip::configure(cs);
    return CircuitConfig { plusc, testc };
  }

  fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
    let test_chip = TestChip::construct(config.testc);
    let x = test_chip.load_private(layouter.namespace(|| "load"), self.x)?;
    let y = test_chip.load_private(layouter.namespace(|| "load"), self.y)?;

    let plus_chip = PlusChip::<F>::construct(config.plusc);
    let z = plus_chip.plus(&mut layouter.namespace(|| "smult"), x, y)?;
    test_chip.expose_public(layouter.namespace(|| "out0"), z, 0)?;

    Ok(())
  }
}
// ANCHOR_END: circuit

#[test]
fn test_plus() {
  use halo2::{dev::MockProver, pasta::Fp};
  let k = 4;

  let circuit = MyCircuit {
    x: Some(Fp::from(1)),
    y: Some(Fp::from(2)),
  };

  let mut public_inputs = vec![Fp::from_u128(3)];

  let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
  assert_eq!(prover.verify(), Ok(()));

  public_inputs[0] += Fp::one();
  let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();
  assert!(prover.verify().is_err());
}
