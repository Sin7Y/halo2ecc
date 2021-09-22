use halo2::{
    arithmetic::FieldExt,
    circuit::{Chip, Layouter},
    plonk::{
        Advice, Column, ConstraintSystem, Fixed,
        Error, Selector
    },
    poly::Rotation,
};

use std::marker::PhantomData;
use crate::types::{Fs, Number};
use crate::utils::*;
use crate::decompose::{DecomposeChip};

pub trait FNorm <Fp: FieldExt, F: FieldExt>: Chip<F> {
    fn normalize (
        &self,
        layouter: &mut impl Layouter<F>,
        x: Fs<F>,
    ) -> Result<Fs<F>, Error>;
}

pub struct FNormChip<Fp: FieldExt, F: FieldExt> {
    config: FNormConfig,
    decompose_chip: DecomposeChip<F>,
    _marker: PhantomData<Fp>,
}

#[derive(Clone, Debug)]
pub struct FNormConfig {
    /// Two fp numbers, three Columns each
    n: Column<Advice>,
    x: Column<Advice>,
    p: Column<Fixed>,
    d: Column<Advice>,
    carry: Column<Advice>,
    sum: Column<Advice>,
    sel: Selector,
}

impl<Fp: FieldExt, F: FieldExt> FNormChip<Fp, F> {
    pub fn construct(config: <Self as Chip<F>>::Config, decompose_chip:DecomposeChip<F>) -> Self {
        Self {
            config,
            decompose_chip,
            _marker: PhantomData,
        }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
    ) -> <Self as Chip<F>>::Config {
        // x = n + p * d
        let n = meta.advice_column();
        let x = meta.advice_column();
        let p = meta.fixed_column();
        let d = meta.advice_column();
        let carry = meta.advice_column();
        let sum = meta.advice_column();

        meta.enable_equality(n.into());
        meta.enable_equality(x.into());
        meta.enable_equality(d.into());
        meta.enable_equality(carry.into());
        meta.enable_equality(sum.into());

        let sel = meta.selector();

        meta.create_gate("fnormalize", |meta| {
            let s = meta.query_selector(sel);

            // pure sum and carry arithment
            // x  | n   | p   | carry | d | sum |
            // x0 | n0  | p0  |   0   | d | r0 + y0 |
            // x1 | n1  | p1  |  c0   | d | r1 + y1 + c0 |
            // x2 | n2  | p2  |  c1   | d | x2 + y2 + c1 |
            let n_cur = meta.query_advice(n, Rotation::cur());
            let p_cur = meta.query_fixed(p, Rotation::cur());
            let carry_cur = meta.query_advice(carry, Rotation::cur());
            let sum_cur = meta.query_advice(sum, Rotation::cur());
            let d_cur = meta.query_advice(d, Rotation::cur());
            vec![ s * (n_cur + p_cur * d_cur + carry_cur - sum_cur)]
        });

        FNormConfig {
            n,
            x,
            d,
            p,
            carry,
            sum,
            sel,
        }
    }
}

impl<Fp: FieldExt, F: FieldExt> Chip<F> for FNormChip<Fp, F> {
    type Config = FNormConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<Fp: FieldExt, F: FieldExt> FNorm<Fp, F> for FNormChip<Fp, F> {
    fn normalize(
        &self,
        layouter: &mut impl Layouter<F>,
        x: Fs<F>,
    ) -> Result<Fs<F>, Error> {
        let config = self.config();
        let xh = x.clone().values[2].value.unwrap();
        let xm = x.clone().values[1].value.unwrap();
        let xl = x.clone().values[0].value.unwrap();

        let x_b = fp_on_fr_to_big_uint::<F>([xl,xm,xh]);
        let p_b = fp_modulus_on_big_uint::<Fp>();
        let [pl, pm, ph] = fp_on_fr_from_big_uint::<F>(p_b.clone());

        let n_b = if x_b.clone() >= p_b.clone()
            { x_b.clone() - p_b.clone() } else { x_b.clone() };
        let d = if x_b >= p_b { F::one() } else { F::zero() };


        let [nl, nm, nh] = fp_on_fr_from_big_uint::<F>(n_b);

        let mut cell = None;

        println!("nl:{:?} pl:{:?} cl:{:?} xl:{:?} d:{:?}", nl, pl, F::zero(), xl, d);

        layouter.assign_region(
            || "load row0",
            |mut region| {
                config.sel.enable(&mut region, 0)?;
                region.assign_advice(
                    || format!("n0"),
                    config.n,
                    0,
                    || Ok(nl),
                )?;

                region.assign_advice(
                    || format!("c0"),
                    config.carry,
                    0,
                    || Ok(F::zero()),
                )?;

                region.assign_advice(
                    || format!("d0"),
                    config.d,
                    0,
                    || Ok(d),
                )?;

                cell = Some (region.assign_advice(
                    || format!("sum_{}", 0),
                    config.sum,
                    0,
                    || Ok(nl + pl * d),
                )?);

                region.assign_advice(
                    || format!("x0"),
                    config.x,
                    0,
                    || Ok(x.clone().values[0].value.unwrap()),
                )?;

                region.assign_fixed(
                    || format!("p0"),
                    config.p,
                    0,
                    || Ok(pl),
                )?;
                Ok(())
            },
        )?;

        let (nl_cell, carry_l) = self.decompose_chip.decompose(
            layouter,
            Number::<F>{cell: cell.unwrap(), value: Some(nl + pl * d)},
            10
        )?;

        let vm = nm + (pm*d) + carry_l.clone().value.unwrap();
        layouter.assign_region(
            || "load row1",
            |mut region| {
                config.sel.enable(&mut region, 0)?;
                region.assign_advice(
                    || format!("n1"),
                    config.n,
                    0,
                    || Ok(nm),
                )?;


                let c = region.assign_advice(
                    || format!("carry_{}", 1),
                    config.carry,
                    0,
                    || Ok(carry_l.clone().value.unwrap()),
                )?;
                region.constrain_equal(carry_l.cell, c)?;

                region.assign_advice(
                    || format!("d0"),
                    config.d,
                    0,
                    || Ok(d),
                )?;

                cell = Some(region.assign_advice(
                   || format!("sum1"),
                   config.sum,
                   0,
                   || Ok(vm),
                )?);

                region.assign_advice(
                    || format!("x1"),
                    config.x,
                    0,
                    || Ok(x.clone().values[1].value.unwrap()),
                )?;

                region.assign_fixed(
                    || format!("p1"),
                    config.p,
                    0,
                    || Ok(pm),
                )?;
                Ok(())
            },
        )?;

        let (nm_cell, carry_m) = self.decompose_chip.decompose(
            layouter,
            Number::<F>{cell: cell.unwrap(), value: Some(vm)},
            10
        )?;

        let vh = nh + ph * d + carry_m.clone().value.unwrap();
        layouter.assign_region(
            || "load row2",
            |mut region| {
                config.sel.enable(&mut region, 0)?;

                region.assign_advice(
                    || format!("n2"),
                    config.n,
                    0,
                    || Ok(nh),
                )?;

                region.assign_advice(
                    || format!("c2"),
                    config.carry,
                    0,
                    || Ok(carry_m.clone().value.unwrap()),
                )?;

                cell = Some (region.assign_advice(
                    || format!("sum2"),
                    config.sum,
                    0,
                    || Ok(vh),
                )?);

                region.assign_advice(
                    || format!("d0"),
                    config.d,
                    0,
                    || Ok(d),
                )?;

                region.assign_advice(
                    || format!("x2"),
                    config.x,
                    0,
                    || Ok(x.clone().values[2].value.unwrap()),
                )?;

                region.assign_fixed(
                    || format!("p2"),
                    config.p,
                    0,
                    || Ok(ph),
                )?;
                Ok(())
            },
        )?;
        let nh_cell = Number::<F> { cell: cell.unwrap(), value:Some(vh) };
        let out = Fs::<F> {values: [nl_cell, nm_cell, nh_cell]};
        Ok(out)
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
        dchip.load_range_table(&mut layouter)?;
        let chip = FNormChip::<Fq, Fp>::construct(config.nconfig, dchip);

        println!("assign region ...");
        let n = chip.normalize(&mut layouter, v)?;
        test_chip.expose_public(layouter.namespace(|| "out"), n.values[0], 0)?;
        test_chip.expose_public(layouter.namespace(|| "out"), n.values[1], 1)?;
        test_chip.expose_public(layouter.namespace(|| "out"), n.values[2], 2)?;
        Ok(())
    }
}

#[test]
fn test_no_overflow() {
    use halo2::dev::MockProver;
    let pub_inputs = vec![
        Fp::from(0x1),
        Fp::from(0x2),
        Fp::from(0x3),
    ];

    let circuit = MyCircuit {
        x0: Fp::from(0x1),
        x1: Fp::from(0x2),
        x2: Fp::from(0x3),
    };
    let prover = MockProver::run(10, &circuit, vec![pub_inputs]).unwrap();
    let presult = prover.verify();
    println!("Error {:?}", presult);

    assert!(presult.is_ok());
}

#[test]
fn test_with_overflow() {
    use halo2::dev::MockProver;
    let pub_inputs = vec![
        Fp::from(0x1),
        Fp::from(0x2),
        Fp::from(0x3),
    ];

    let circuit = MyCircuit {
        x0: Fp::from(0x1),
        x1: Fp::from(0x2),
        x2: Fp::from(0x3),
    };
    let prover = MockProver::run(10, &circuit, vec![pub_inputs]).unwrap();
    let presult = prover.verify();
    println!("Error {:?}", presult);

    assert!(presult.is_ok());
}
