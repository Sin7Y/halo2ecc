// Plus chip for filed plus on F_r that does not exceed r
// Given a sequence of cells, calculated the sum of the cells
// and then output the carry and remainder of the sum

extern crate halo2;

use std::marker::PhantomData;
use crate::types::Number;
use crate::testchip::{TestChip, TestChipTrait, TestConfig};

use halo2::{
    arithmetic::FieldExt,
    circuit::{Cell, Chip, Layouter, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Instance, Selector},
    poly::Rotation,
};
use halo2::{dev::MockProver, pasta::Fp};



#[derive(Clone, Debug)]
struct ShortPlusConfig {
    /// Two fp numbers, three Columns each
    advice: Column<Advice>,
    sum: Column<Advice>,
    carry: Column<Advice>,
    sel: Selector,
}

trait ShortPlus <F: FieldExt>: Chip<F> {
    /// Variable representing a number.
    fn sum (
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

        meta.enable_equality(carry.into());
        meta.enable_equality(sum.into());
        meta.enable_equality(advice.into());

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
            sum,
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
                println!("xixi");
                for (p, e) in inputs.iter().enumerate() {
                    let sum_cell = region.assign_advice(
                        || format!("s_{}", pos),
                        config.advice,
                        p,
                        || Ok(sum),
                    )?;
                    let cell = region.assign_advice(
                        || format!("operand_{}", pos),
                        config.sum,
                        p,
                        || e.value.ok_or(Error::SynthesisError),
                    )?;
                    region.constrain_equal(e.cell, cell)?;
                    sum = sum + e.value.unwrap();
                    config.sel.enable(&mut region, pos)?;
                    pos += 1;
                    // missing selector enabling
                }
                let cell = region.assign_advice(
                    || format!("s_{}", pos),
                    config.advice,
                    pos,
                    || Ok(sum),
                )?;
                final_sum = Some (Number {cell, value:Some(sum),});
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

    fn sum (
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

#[derive(Clone, Debug)]
struct TestCircConfig {
    pconfig: ShortPlusConfig,
    tconfig: TestConfig,
}

impl Circuit<Fp> for TestCircuit {
    type Config = TestCircConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
      Self::default()
    }

    fn configure(cs: &mut ConstraintSystem<Fp>) -> Self::Config {
        TestCircConfig {
            pconfig: ShortPlusChip::<Fp>::configure(cs),
            tconfig: TestChip::<Fp>::configure(cs),
        }
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<Fp>) -> Result<(), Error> {
        println!("Start synthesize ...");
        let test_chip = TestChip::<Fp>::construct(config.tconfig);
        let mut cells = vec![];
        for i in &self.inputs {
            let cell = test_chip.load_private(layouter.namespace(|| "cell"), Some(*i))?;
            cells.push(cell);
        }
        let op_chip:ShortPlusChip<Fp> = ShortPlusChip::<Fp>::construct(config.pconfig);
        let output_cell = op_chip.assign_region(&mut layouter, cells)?;
        test_chip.expose_public(layouter.namespace(|| "expose c"), output_cell, 0);
        println!("AllocPrivate ... Done");
        Ok(())
    }
}

#[test]
fn circuit() {
    // The number of rows used in the constraint system matrix.
    const PUB_INPUT: u64 = 3;

    let mut pub_inputs = vec![Fp::from(6)];

    let circuit = TestCircuit {
        inputs: vec![Fp::from(1), Fp::from(2), Fp::from(3)]
    };
    let prover = MockProver::run(5, &circuit, vec![pub_inputs]).unwrap();
    let presult = prover.verify();
    println!("Error {:?}", presult);

    assert!(presult.is_ok());

}

