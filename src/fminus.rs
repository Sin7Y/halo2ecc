use halo2::{
    arithmetic::FieldExt,
    circuit::{Chip, Layouter},
    plonk::{
        Advice, Column, ConstraintSystem, Error
    },
};

use std::marker::PhantomData;
use crate::fplus::{FPlusChip, FPlusConfig, FPlus};
use crate::types::{Fs, Number};
use crate::utils::*;
use crate::decompose::{DecomposeChip};

pub trait FMinus <Fp: FieldExt, F: FieldExt>: Chip<F> {
    fn minus(
        &self,
        layouter: &mut impl Layouter<F>,
        x: Fs<F>,
        y: Fs<F>,
    ) -> Result<Fs<F>, Error>;
}

pub struct FMinusChip<Fp: FieldExt, F: FieldExt> {
    config: FMinusConfig,
    fplus_chip: FPlusChip<Fp, F>,
    _marker: PhantomData<Fp>,
}

#[derive(Clone, Debug)]
pub struct FMinusConfig {
    /// Two fp numbers, three Columns each
    x: Column<Advice>,
    y: Column<Advice>,
    result: Column<Advice>,
}

impl<Fp: FieldExt, F: FieldExt> FMinusChip<Fp, F> {
    pub fn construct(
        config: <Self as Chip<F>>::Config,
        fplus_chip:FPlusChip<Fp, F>) -> Self {
        Self {
            config,
            fplus_chip,
            _marker: PhantomData,
        }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
    ) -> <Self as Chip<F>>::Config {
        let x = meta.advice_column();
        let y = meta.advice_column();
        let result = meta.advice_column();

        meta.enable_equality(x.into());
        meta.enable_equality(y.into());
        meta.enable_equality(result.into());

        FMinusConfig {
            x,
            y,
            result,
        }
    }
}

impl<Fp: FieldExt, F: FieldExt> Chip<F> for FMinusChip<Fp, F> {
    type Config = FMinusConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<Fp: FieldExt, F: FieldExt> FMinus<Fp, F> for FMinusChip<Fp, F> {
    fn minus(
        &self,
        layouter: &mut impl Layouter<F>,
        x: Fs<F>,
        y: Fs<F>,
    ) -> Result<Fs<F>, Error> {
        let config = self.config();
        let xh = x.clone().values[2].value.unwrap();
        let xm = x.clone().values[1].value.unwrap();
        let xl = x.clone().values[0].value.unwrap();

        let x_b = fp_on_fr_to_big_uint::<F>([xl,xm,xh]);

        let yh = y.clone().values[2].value.unwrap();
        let ym = y.clone().values[1].value.unwrap();
        let yl = y.clone().values[0].value.unwrap();

        let y_b = fp_on_fr_to_big_uint::<F>([yl,ym,yh]);
        let p_b = fp_modulus_on_big_uint::<Fp>();

        let r_b = if x_b.clone() >= y_b.clone()
            { x_b.clone() - y_b.clone() } else { x_b.clone() + p_b - y_b };

        let [rl, rm, rh] = fp_on_fr_from_big_uint::<F>(r_b);

        let mut fs_r = None;
        let mut fs_x = None;
        let mut fs_y = None;

        layouter.assign_region(
            || "minus region",
            |mut region| {
                fs_r = Some (Fs::<F> {
                    values: [
                        Number::<F> {
                            cell: (region.assign_advice(
                                || format!("rl"),
                                config.result,
                                0,
                                || Ok(rl),
                            )?),
                            value: Some (rl)
                        },
                        Number::<F> {
                            cell: (region.assign_advice(
                                || format!("rm"),
                                config.result,
                                0,
                                || Ok(rm),
                            )?),
                            value: Some (rm)
                        },
                        Number::<F> {
                            cell: (region.assign_advice(
                                || format!("rh"),
                                config.result,
                                0,
                                || Ok(rh),
                            )?),
                            value: Some (rh)
                        },
                    ]
                });

                fs_x = Some (Fs::<F> {
                    values: [
                        Number::<F> {
                            cell: (region.assign_advice(
                                || format!("xl"),
                                config.x,
                                0,
                                || Ok(xl),
                            )?),
                            value: Some (xl)
                        },
                        Number::<F> {
                            cell: (region.assign_advice(
                                || format!("xm"),
                                config.x,
                                0,
                                || Ok(xm),
                            )?),
                            value: Some (xm)
                        },
                        Number::<F> {
                            cell: (region.assign_advice(
                                || format!("xh"),
                                config.x,
                                0,
                                || Ok(xh),
                            )?),
                            value: Some (xh)
                        },
                    ]
                });

                fs_y = Some (Fs::<F> {
                    values: [
                        Number::<F> {
                            cell: (region.assign_advice(
                                || format!("yl"),
                                config.y,
                                0,
                                || Ok(yl),
                            )?),
                            value: Some (yl)
                        },
                        Number::<F> {
                            cell: (region.assign_advice(
                                || format!("ym"),
                                config.y,
                                0,
                                || Ok(ym),
                            )?),
                            value: Some (ym)
                        },
                        Number::<F> {
                            cell: (region.assign_advice(
                                || format!("yh"),
                                config.y,
                                0,
                                || Ok(yh),
                            )?),
                            value: Some (yh)
                        },
                    ]
                });
                Ok(())
            },
        )?;

        let fs_xc =
            self.fplus_chip.plus(layouter, fs_y.unwrap(), fs_r.clone().unwrap())?;

        layouter.assign_region(
            || "minus region",
            |mut region| {
                constrain_fs(&mut region, &fs_xc, &(fs_x.unwrap()))?;
                Ok(())
            },
        )?;
        Ok(fs_r.unwrap())
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
    y0: Fp,
    y1: Fp,
    y2: Fp,
}

#[derive(Clone, Debug)]
struct TestCircConfig {
    mconfig: FMinusConfig,
    pconfig: FPlusConfig,
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
            mconfig: FMinusChip::<Fq, Fp>::configure(cs),
            pconfig: FPlusChip::<Fq, Fp>::configure(cs),
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

        let x = Fs::<Fp> {values: [
                Number::<Fp>{cell:c0.cell, value:Some(self.x0)},
                Number::<Fp>{cell:c1.cell, value:Some(self.x1)},
                Number::<Fp>{cell:c2.cell, value:Some(self.x2)},
        ]};

        let c3 = test_chip.load_private(layouter.namespace(|| "cell"), Some(self.y0))?;
        let c4 = test_chip.load_private(layouter.namespace(|| "cell"), Some(self.y1))?;
        let c5 = test_chip.load_private(layouter.namespace(|| "cell"), Some(self.y2))?;

        let y = Fs::<Fp> {values: [
                Number::<Fp>{cell:c3.cell, value:Some(self.y0)},
                Number::<Fp>{cell:c4.cell, value:Some(self.y1)},
                Number::<Fp>{cell:c5.cell, value:Some(self.y2)},
        ]};


        let dchip = DecomposeChip::<Fp>::constructor(config.dconfig);
        dchip.load_range_table(&mut layouter)?;
        let fplus_chip = FPlusChip::<Fq, Fp>::construct(config.pconfig, dchip);
        let fminus_chip = FMinusChip::<Fq, Fp>::construct(config.mconfig, fplus_chip);

        println!("assign region ...");
        let sum = fminus_chip.minus(&mut layouter, x, y)?;
        test_chip.expose_public(layouter.namespace(|| "out"), sum.values[0], 0)?;
        test_chip.expose_public(layouter.namespace(|| "out"), sum.values[1], 1)?;
        test_chip.expose_public(layouter.namespace(|| "out"), sum.values[2], 2)?;
        Ok(())
    }
}

#[test]
fn fminus_test_0() {
    use halo2::dev::MockProver;
    let pub_inputs = vec![
        Fp::from(0x0),
        Fp::from(0x0),
        Fp::from(0x0),
    ];

    let circuit = MyCircuit {
        x0: Fp::from(0x1),
        x1: Fp::from(0x2),
        x2: Fp::from(0x3),
        y0: Fp::from(0x1),
        y1: Fp::from(0x2),
        y2: Fp::from(0x3),
    };
    let prover = MockProver::run(10, &circuit, vec![pub_inputs]).unwrap();
    let presult = prover.verify();
    println!("Error {:?}", presult);

    assert!(presult.is_ok());
}
