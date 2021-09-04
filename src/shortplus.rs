extern crate halo2;

use std::marker::PhantomData;
use crate::types::Number;

use halo2::{
    arithmetic::FieldExt,
    circuit::{Cell, Chip, Layouter, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Instance, Selector},
    poly::Rotation,
};
use halo2::{dev::MockProver, pasta::Fp};

trait ShortPlus <F: FieldExt>: Chip<F> {
    /// Variable representing a number.
    fn perform(
        &self,
        layouter: impl Layouter<F>,
        inputs: Vec<Number<F>>,
    ) -> Result<Number<F>, Error>;

    fn expose_carry_remainder(
        &self,
        layouter: impl Layouter<F>,
        remainder: Number<F>,
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

        // Calculate the sum of a list of operands
        // | col0   |  col1   |
        // |--------|---------|
        // | sum_k  | operand |
        // | sum_kplus |      |

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

    fn assign_region(&self,
        layouter: &mut impl Layouter<F>,
        inputs: Vec<Number<F>>
    ) -> Result<Number<F>, Error> {
        let config = self.config();
        let mut sum = F::from(0);
        let mut pos = 0;
        let mut final_sum = None;
        layouter.assign_region(
            || "load private",
            |mut region| {
                for (p, e) in inputs.iter().enumerate() {
                    let sum_cell = region.assign_advice(
                        || format!("s_{}", pos),
                        config.advice,
                        p,
                        || Ok(sum),
                    )?;
                    let cell = region.assign_advice(
                        || format!("operand_{}", pos),
                        config.advice,
                        p,
                        || e.value.ok_or(Error::SynthesisError),
                    )?;
                    region.constrain_equal(e.cell, cell)?;
                    sum = sum + e.value.unwrap();
                    pos += 1;
                }
                let cell = region.assign_advice(
                    || format!("s_{}", pos),
                    config.advice,
                    pos,
                    || Ok(sum),
                )?;
                let final_sum = Some (Number {cell, value:Some(sum),});
                Ok(())
            },
        )?;
        Ok(final_sum.unwrap())
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

    fn expose_carry_remainder(
        &self,
        mut layouter: impl Layouter<F>,
        remainder: Number<F>,
    ) -> Result<(), Error> {
        // the final sum = carry * 2^d + remainder
        Ok(())
    }

    fn perform(
        &self,
        mut layouter: impl Layouter<F>,
        inputs: Vec<Number<F>>,
    ) -> Result<Number<F>, Error> {
        let mut out = None;
        Ok(out.unwrap())
    }
}

#[derive(Clone, Default)]
struct TestCircuit {
    inputs: Vec<Fp>,
}

impl Circuit<Fp> for TestCircuit {
    type Config = ShortPlusConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
      Self::default()
    }

    fn configure(cs: &mut ConstraintSystem<Fp>) -> Self::Config {
        ShortPlusChip::<Fp>::configure(cs)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<Fp>) -> Result<(), Error> {
        println!("Start synthesize ...");
        let op_chip:ShortPlusChip<Fp> = ShortPlusChip::<Fp>::construct(config);
        op_chip.assign_region(&mut layouter, self.inputs)?;
        println!("AllocPrivate ... Done");
        Ok(())
    }
}

#[test]
fn circuit() {
    // The number of rows used in the constraint system matrix.
    const PUB_INPUT: u64 = 3;

    let mut pub_inputs = vec![Fp::zero()];

    let circuit = TestCircuit {
        inputs: vec![Fp::from(1), Fp::from(2), Fp::from(3)]
    };
    let prover = MockProver::run(5, &circuit, vec![]).unwrap();
    let presult = prover.verify();
    println!("Error {:?}", presult);

    assert!(presult.is_ok());

}

