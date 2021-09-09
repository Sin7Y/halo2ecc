use halo2::{
    arithmetic::FieldExt,
    circuit::{Chip, Layouter, Region, Cell},
    plonk::{
        Advice, Column, ConstraintSystem,
        Error, Instance,
        Selector, Expression
    },
    poly::Rotation,
};

use std::marker::PhantomData;
use crate::types::{Fs, FsAdvice, Number};
use crate::utils::*;
use crate::decompose::{DecomposeChip};
use ff::PrimeFieldBits;

trait FNorm <Fp: FieldExt, F: FieldExt + PrimeFieldBits>: Chip<F> {
    fn normalize (
        &self,
        layouter: &mut impl Layouter<F>,
        x: Fs<F>,
        y: Fs<F>,
    ) -> Result<(Fs<F>, Number<F>), Error>;
}

struct FNormChip<Fp: FieldExt, F: FieldExt + PrimeFieldBits> {
    config: FNormConfig,
    decompose_chip: DecomposeChip<F>,
    _marker: PhantomData<Fp>,
}

#[derive(Clone, Debug)]
struct FNormConfig {
    /// Two fp numbers, three Columns each
    op1: Column<Advice>,
    op2: Column<Advice>,
    carry: Column<Advice>,
    sum: Column<Advice>,
    remainder: Column<Advice>,
    sel: Selector,
}

impl<Fp: FieldExt, F: FieldExt + PrimeFieldBits> FNormChip<Fp, F> {
    fn construct(config: <Self as Chip<F>>::Config, decompose_chip:DecomposeChip<F>) -> Self {
        Self {
            config,
            decompose_chip,
            _marker: PhantomData,
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
    ) -> <Self as Chip<F>>::Config {
        let op1 = meta.advice_column();
        let op2 = meta.advice_column();
        let carry = meta.advice_column();
        let sum = meta.advice_column();
        let remainder = meta.advice_column();

        meta.enable_equality(op1.into());
        meta.enable_equality(op2.into());
        meta.enable_equality(carry.into());
        meta.enable_equality(sum.into());
        meta.enable_equality(remainder.into());

        let sel = meta.selector();

        meta.create_gate("mult-split", |meta| {
            let s = meta.query_selector(sel);

            // pure sum and carry arithment
            // | op1 | op2 | carry | sum | remainder |
            // | x0  | y0  |   0   | x0 + y0 | v0
            // | x1  | y1  |  c0   | x1 + y1 + c0 | v_1 |
            // | x2  | y2  |  c1   | x2 + y2 + c1 | v_2 |
            // | 0   | 0   |  c2   |     |      |
            let op1_cur = meta.query_advice(op1, Rotation::cur());
            let op2_cur = meta.query_advice(op2, Rotation::cur());
            let carry_cur = meta.query_advice(carry, Rotation::cur());
            let sum_cur = meta.query_advice(sum, Rotation::cur());
            vec![ s * (op1_cur + op2_cur +carry_cur - sum_cur) ]
        });

        FNormConfig {
            op1,
            op2,
            carry,
            sum,
            remainder,
            sel,
        }
    }
}

impl<Fp: FieldExt, F: FieldExt + PrimeFieldBits> Chip<F> for FNormChip<Fp, F> {
    type Config = FNormConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<Fp: FieldExt, F: FieldExt + PrimeFieldBits> FNorm<Fp, F> for FNormChip<Fp, F> {
    fn normalize(
        &self,
        layouter: &mut impl Layouter<F>,
        x: Fs<F>,
        y: Fs<F>,
    ) -> Result<(Fs<F>, Number<F>), Error> {
        let config = self.config();
        let xh = x.clone().values[2].value.unwrap();
        let xm = x.clone().values[1].value.unwrap();
        let xl = x.clone().values[0].value.unwrap();

        let yh = y.clone().values[2].value.unwrap();
        let ym = y.clone().values[1].value.unwrap();
        let yl = y.clone().values[0].value.unwrap();

        let mut out = None;
        let mut cell = None;

        layouter.assign_region(
            || "load row0",
            |mut region| {
                region.assign_advice(
                    || format!("carry_{}", 0),
                    config.carry,
                    0,
                    || Ok(F::zero()),
                )?;

                cell = Some (region.assign_advice(
                    || format!("sum_{}", 0),
                    config.sum,
                    0,
                    || Ok(xl + yl),
                )?);

                region.assign_advice(
                    || format!("op_{}", 0),
                    config.op1,
                    0,
                    || Ok(x.clone().values[0].value.unwrap()),
                )?;

                region.assign_advice(
                    || format!("op_{}", 0),
                    config.op2,
                    0,
                    || Ok(y.clone().values[0].value.unwrap()),
                )?;
                Ok(())
            },
        )?;

        let (sum_l, carry_l) =
            self.decompose_chip.decompose(layouter, Number::<F>{cell: cell.unwrap(), value: Some(xl+yl)}, 10)?;

        let vm = xm + ym + carry_l.clone().value.unwrap();
        layouter.assign_region(
            || "load row0",
            |mut region| {
                region.assign_advice(
                    || format!("carry_{}", 1),
                    config.carry,
                    0,
                    || Ok(carry_l.clone().value.unwrap()),
                )?;

                let cell = Some(region.assign_advice(
                   || format!("sum_{}", 1),
                   config.sum,
                   0,
                   || Ok(vm),
                )?);

                region.assign_advice(
                    || format!("op_{}", 1),
                    config.op1,
                    0,
                    || Ok(x.clone().values[1].value.unwrap()),
                )?;

                region.assign_advice(
                    || format!("op_{}", 1),
                    config.op2,
                    0,
                    || Ok(y.clone().values[1].value.unwrap()),
                )?;
                Ok(())
            },
        )?;
        let (sum_m, carry_m) =
            self.decompose_chip.decompose(layouter, Number::<F>{cell: cell.unwrap(), value: Some(vm) }, 10)?;

        let vh = xh + yh + carry_m.clone().value.unwrap();
        layouter.assign_region(
            || "load row0",
            |mut region| {
                region.assign_advice(
                    || format!("carry_{}", 2),
                    config.carry,
                    0,
                    || Ok(carry_m.clone().value.unwrap()),
                )?;

                let cell = (region.assign_advice(
                    || format!("sum_{}", 2),
                    config.sum,
                    2,
                    || Ok(vh),
                )?);
                region.assign_advice(
                    || format!("op_{}", 2),
                    config.op1,
                    0,
                    || Ok(x.clone().values[2].value.unwrap()),
                )?;

                region.assign_advice(
                    || format!("op_{}", 2),
                    config.op2,
                    0,
                    || Ok(y.clone().values[2].value.unwrap()),
                )?;
                Ok(())
            },
        )?;
        let (sum_h, carry_h) =
            self.decompose_chip.decompose(layouter, Number::<F>{cell: cell.unwrap(), value: Some(vh) }, 16)?;

        out = Some (Fs::<F> {values: [sum_l, sum_m, sum_h]});
        Ok((out.unwrap(), carry_h))
    }
}

use halo2::pasta::{Fp, Fq};
use crate::testchip::*;
use crate::decompose::*;
use halo2::plonk::Circuit;
use halo2::circuit::SimpleFloorPlanner;

#[derive(Clone, Default)]
struct MyCircuit {
    x0: Fp,
    x1: Fp,
    x2: Fp,
    o0: Fp,
    o1: Fp,
    o2: Fp,
    carry: Fp,
}

#[derive(Clone, Debug)]
struct TestCircConfig {
    nconfig: FNormConfig,
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
            nconfig: FNormChip::<Fq, Fp>::configure(cs),
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
        let c1 = test_chip.load_private(layouter.namespace(|| "cell"), Some(self.x1))?;
        let c2 = test_chip.load_private(layouter.namespace(|| "cell"), Some(self.x2))?;

        let v = Fs::<Fp> {values: [
                Number::<Fp>{cell:c0.cell, value:Some(self.x0)},
                Number::<Fp>{cell:c1.cell, value:Some(self.x1)},
                Number::<Fp>{cell:c2.cell, value:Some(self.x2)},
        ]};
        let dchip = DecomposeChip::<Fp>::constructor(config.dconfig);
        dchip.load_range_table(&mut layouter);
        let chip = FNormChip::<Fq, Fp>::construct(config.nconfig, dchip);

        println!("assign region ...");
        let (sum, carry) = chip.normalize(&mut layouter, v.clone(), v)?;
        test_chip.expose_public(layouter.namespace(|| "out"), sum.values[0], 0)?;
        test_chip.expose_public(layouter.namespace(|| "out"), sum.values[1], 1)?;
        test_chip.expose_public(layouter.namespace(|| "out"), sum.values[2], 2)?;
        test_chip.expose_public(layouter.namespace(|| "out"), carry, 3)?;
        Ok(())
    }
}

#[test]
fn check() {
    use halo2::dev::MockProver;
    let pub_inputs = vec![
        Fp::from(0x2),
        Fp::from(0x2),
        Fp::from(0x2),
        Fp::from(0x0),
    ];

    let circuit = MyCircuit {
        x0: Fp::from(0x1),
        x1: Fp::from(0x1),
        x2: Fp::from(0x1),
        o0: Fp::from(0x2),
        o1: Fp::from(0x2),
        o2: Fp::from(0x2),
        carry: Fp::from(0x0)
    };
    let prover = MockProver::run(10, &circuit, vec![pub_inputs]).unwrap();
    let presult = prover.verify();
    println!("Error {:?}", presult);

    assert!(presult.is_ok());
}
