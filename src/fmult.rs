use halo2::{
    arithmetic::FieldExt,
    circuit::{Cell, Chip, Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Instance, Selector},
    poly::Rotation,
};

use crate::decompose::{DecomposeChip, DecomposeConfig};
use crate::fnormalize::{FNorm, FNormChip, FNormConfig};
use crate::plus::{Plus, PlusChip, PlusConfig};
use crate::shortmult::{ShortMult, ShortMultChip, ShortMultConfig};
use crate::types::{Fs, FsAdvice, Number};
use crate::utils::*;
use ff::PrimeFieldBits;
use std::marker::PhantomData;

trait FMult<Fp: FieldExt, F: FieldExt>: Chip<F> {
    fn mult(&self, layouter: &mut impl Layouter<F>, a: Fs<F>, b: Fs<F>) -> Result<Fs<F>, Error>;
}

struct FMultChip<Fp: FieldExt, F: FieldExt> {
    config: FMultConfig<F>,
    smult_chip: ShortMultChip<Fp, F>,
    decom_chip: DecomposeChip<F>,
    plus_chip: PlusChip<F>,
    fnorm_chip: FNormChip<Fp, F>,
    _marker: PhantomData<F>,
}

#[derive(Clone, Debug)]
struct FMultConfig<F: FieldExt> {
    /// Two fp numbers, three Columns each
    x: FsAdvice<F>,
    y: FsAdvice<F>,
    output: [Column<Advice>; 4],
    sel: Selector,

    advice: Column<Advice>,
    constant: Column<Fixed>,
}

impl<Fp: FieldExt, F: FieldExt> FMultChip<Fp, F> {
    fn construct(
        config: <Self as Chip<F>>::Config,
        smult_chip: ShortMultChip<Fp, F>,
        decom_chip: DecomposeChip<F>,
        plus_chip: PlusChip<F>,
        fnorm_chip: FNormChip<Fp, F>,
    ) -> Self {
        Self {
            config,
            smult_chip,
            decom_chip,
            plus_chip,
            fnorm_chip,
            _marker: PhantomData,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> FMultConfig<F> {
        let advice = meta.advice_column();
        meta.enable_equality(advice.into());

        let constant = meta.fixed_column();
        meta.enable_constant(constant);

        let sel = meta.selector();

        let x = FsAdvice::<F> {
            advices: [
                meta.advice_column(),
                meta.advice_column(),
                meta.advice_column(),
            ],
            _marker: PhantomData,
        };

        let y = FsAdvice::<F> {
            advices: [
                meta.advice_column(),
                meta.advice_column(),
                meta.advice_column(),
            ],
            _marker: PhantomData,
        };

        let output = [
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
        ];

        for i in 0..3 {
            meta.enable_equality(x.advices[i].into());
            meta.enable_equality(y.advices[i].into());
        }

        for i in 0..4 {
            meta.enable_equality(output[i].into());
        }

        meta.create_gate("mult-split", |meta| {
            let s = meta.query_selector(sel);
            // Controlled by init_sel
            // | xl | xm | xh | yl | ym | yh | zl | zm | zh

            let xh = meta.query_advice(x.advices[2], Rotation::cur());
            let xm = meta.query_advice(x.advices[1], Rotation::cur());
            let xl = meta.query_advice(x.advices[0], Rotation::cur());
            let yh = meta.query_advice(y.advices[2], Rotation::cur());
            let ym = meta.query_advice(y.advices[1], Rotation::cur());
            let yl = meta.query_advice(y.advices[0], Rotation::cur());
            let o3 = meta.query_advice(output[3], Rotation::cur());
            let o2 = meta.query_advice(output[2], Rotation::cur());
            let o1 = meta.query_advice(output[1], Rotation::cur());
            let o0 = meta.query_advice(output[0], Rotation::cur());

            let shift_80 = Expression::Constant(pow2::<F>(80));
            let shift_160 = Expression::Constant(pow2::<F>(160));

            vec![
                s.clone()
                    * (o0
                        - (xl.clone() * yl.clone()
                            + (xm.clone() * yl.clone() + xl.clone() * ym.clone()) * shift_80)),
                s.clone()
                    * (o1
                        - (xm.clone() * ym.clone()
                            + xh.clone() * yl.clone()
                            + xl.clone() * yh.clone())),
                s.clone() * (o2 - (xm.clone() * yh.clone() + xh.clone() * ym.clone())),
                s.clone() * (o3 - (xh.clone() * yh.clone())),
            ]
        });

        return FMultConfig {
            x,
            y,
            output,
            sel,
            advice,
            constant,
        };
    }

    fn assign_fs(
        &self,
        region: &mut Region<F>,
        a: FsAdvice<F>,
        o: [F; 3],
        row_offset: usize,
        hint: &str,
    ) -> Fs<F> {
        let mut cells = [None, None, None];

        for i in 0..3 {
            let cell = region
                .assign_advice(
                    || format!("{}_{}", hint, i),
                    a.advices[i],
                    row_offset,
                    || Ok(o[i]),
                )
                .unwrap();
            cells[i] = Some(Number::<F> {
                cell,
                value: Some(o[i]),
            });
        }

        Fs::<F> {
            values: [cells[0].unwrap(), cells[1].unwrap(), cells[2].unwrap()],
        }
    }
}

impl<Fp: FieldExt, F: FieldExt> Chip<F> for FMultChip<Fp, F> {
    type Config = FMultConfig<F>;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<Fp: FieldExt, F: FieldExt> FMultChip<Fp, F> {
    fn check_constant(
        &self,
        layouter: &mut impl Layouter<F>,
        input: Number<F>,
        constant: F,
    ) -> Result<(), Error> {
        let config = self.config();

        layouter.assign_region(
            || "load constant",
            |mut region| {
                let _cell = region.assign_advice_from_constant(
                    || "check constant value",
                    config.advice,
                    0,
                    constant,
                )?;
                region.constrain_equal(input.cell, _cell)?;
                Ok(())
            },
        )?;

        Ok(())
    }

    fn load_constant(
        &self,
        layouter: &mut impl Layouter<F>,
        constant: F,
    ) -> Result<Number<F>, Error> {
        let config = self.config();

        let mut num = None;
        layouter.assign_region(
            || "load constant",
            |mut region| {
                let cell = region.assign_advice_from_constant(
                    || "load constant value",
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
    fn l1mult(
        &self,
        layouter: &mut impl Layouter<F>,
        a: Fs<F>,
        b: Fs<F>,
    ) -> Result<[Number<F>; 4], Error> {
        let config = self.config();
        let mut ooutput = None;

        layouter.assign_region(
            || "load private",
            |mut region| {
                let xh = a.clone().values[2].value.unwrap();
                let xm = a.clone().values[1].value.unwrap();
                let xl = a.clone().values[0].value.unwrap();

                let yh = b.clone().values[2].value.unwrap();
                let ym = b.clone().values[1].value.unwrap();
                let yl = b.clone().values[0].value.unwrap();

                let shift_80 = pow2::<F>(80);
                let shift_160 = pow2::<F>(160);

                let mut output = [F::zero(), F::zero(), F::zero(), F::zero()];

                output[3] = xh.clone() * yh.clone();
                output[2] = xh * ym.clone() + xm.clone() * yh;
                output[1] =
                    xh.clone() * yl.clone() + xm.clone() * ym.clone() + xl.clone() * yh.clone();
                output[0] = (xl * ym + xm * yl) * shift_80 + xl.clone() * yl.clone();

                let _ = self.assign_fs(&mut region, config.x, [xl, xm, xh], 0, "fmult-x");
                let _ = self.assign_fs(&mut region, config.y, [yl, ym, yh], 0, "fmult-y");

                let mut output_cells: Vec<Cell> = vec![];
                for i in 0..4 {
                    let cell = region.assign_advice(
                        || "load constant value",
                        config.output[i],
                        0,
                        || Ok(output[i]),
                    )?;
                    output_cells.push(cell);
                }

                ooutput = Some([
                    Number {
                        cell: output_cells[0],
                        value: Some(output[0]),
                    },
                    Number {
                        cell: output_cells[1],
                        value: Some(output[1]),
                    },
                    Number {
                        cell: output_cells[2],
                        value: Some(output[2]),
                    },
                    Number {
                        cell: output_cells[3],
                        value: Some(output[3]),
                    },
                ]);

                Ok(())
            },
        )?;

        return Ok(ooutput.unwrap());
    }
}

impl<Fp: FieldExt, F: FieldExt> FMult<Fp, F> for FMultChip<Fp, F> {
    fn mult(&self, layouter: &mut impl Layouter<F>, a: Fs<F>, b: Fs<F>) -> Result<Fs<F>, Error> {
        println!("a = {:?}", a.values);
        println!("b = {:?}", b.values);

        let l1output = self.l1mult(layouter, a, b)?;
        let (l, rem) = self.decom_chip.decompose(layouter, l1output[0], 10)?;
        let (m, h) = self.decom_chip.decompose(layouter, rem, 10)?;

        println!("l1output = {:?}", l1output);

        // For x * 2 ** 160 part, we split into x1 * 2 ** 240 + x2 * 160 (x2 < 2 ** 80),
        // Thus, we can directly add x2 to high field of l1output[0] and add x1 to l1output[2];
        let (l1ouptput1_l, l1output1_h) = self.decom_chip.decompose(layouter, l1output[1], 10)?;
        let h = self.plus_chip.plus(layouter, h, l1ouptput1_l)?;
        let l1output2 = self.plus_chip.plus(layouter, l1output[2], l1output1_h)?;

        let (l2output, rem) =
            self.smult_chip
                .constrain(layouter, l1output2, Fs { values: [l, m, h] }, 32, 0)?;

        println!("l2output = {:?}", l2output);

        let rem = self.plus_chip.plus(layouter, rem, l1output[3])?;
        let (l3output, rem) = self.smult_chip.constrain(layouter, rem, l2output, 24, 10)?;

        println!("rem {:?}", rem);

        println!("l3output = {:?}", l3output);

        self.check_constant(layouter, rem, F::zero())?;

        let zero_cell = self.load_constant(layouter, F::zero())?;
        let (l4output, carry) = self.fnorm_chip.normalize(
            layouter,
            l3output,
            Fs {
                values: [zero_cell, zero_cell, zero_cell],
            },
        )?;

        // round 1
        let (l4output, res) = self.smult_chip.constrain(layouter, carry, l4output, 1, 2)?;
        let (l4output, carry) = self.fnorm_chip.normalize(
            layouter,
            l4output,
            Fs {
                values: [zero_cell, zero_cell, zero_cell],
            },
        )?;
        self.check_constant(layouter, res, F::zero())?;

        // round 2
        let (l4output, res) = self.smult_chip.constrain(layouter, carry, l4output, 1, 2)?;
        let (l4output, carry) = self.fnorm_chip.normalize(
            layouter,
            l4output,
            Fs {
                values: [zero_cell, zero_cell, zero_cell],
            },
        )?;
        self.check_constant(layouter, res, F::zero())?;

        // round 3
        let (l4output, res) = self.smult_chip.constrain(layouter, carry, l4output, 1, 2)?;
        let (l4output, carry) = self.fnorm_chip.normalize(
            layouter,
            l4output,
            Fs {
                values: [zero_cell, zero_cell, zero_cell],
            },
        )?;
        self.check_constant(layouter, res, F::zero())?;
        self.check_constant(layouter, carry, F::zero())?;

        Ok(l4output)
    }
}

use crate::byteoptable::*;
use crate::testchip::*;
use halo2::circuit::SimpleFloorPlanner;
use halo2::pasta::{Fp, Fq};
use halo2::plonk::Circuit;

#[derive(Clone, Default)]
struct MyCircuit {
    inputs: [Fp; 6],
}

#[derive(Clone, Debug)]
pub struct CircuitConfig {
    bconf: ByteOpChipConfig,
    pconf: PlusConfig,
    sconf: ShortMultConfig,
    dconf: DecomposeConfig<Fp>,
    tconf: TestConfig,
    nconf: FNormConfig,
    mconf: FMultConfig<Fp>,
}

const CHUNCK_BITS: usize = 8;
const L_RANGE: usize = 1 << CHUNCK_BITS;
const R_RANGE: usize = 256 * 2 / CHUNCK_BITS;
const S_RANGE: usize = 3;

impl Circuit<Fp> for MyCircuit {
    // Since we are using a single chip for everything, we can just reuse its config.
    type Config = CircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }
    fn configure(cs: &mut ConstraintSystem<Fp>) -> Self::Config {
        let table_col = cs.lookup_table_column();
        let bconf = ByteOpChip::<Fp, Fq, ShiftOp>::configure(cs);
        let pconf = PlusChip::<Fp>::configure(cs);
        let sconf = ShortMultChip::<Fq, Fp>::configure(
            cs,
            bconf.tbl_l,
            bconf.tbl_r,
            bconf.tbl_s,
            bconf.tbl_o,
        );
        let mconf = FMultChip::<Fq, Fp>::configure(cs);
        let nconf = FNormChip::<Fq, Fp>::configure(cs);
        let dconf = DecomposeChip::<Fp>::configure(cs, table_col);
        let tconf = TestChip::configure(cs);
        return CircuitConfig {
            bconf,
            pconf,
            sconf,
            dconf,
            nconf,
            tconf,
            mconf,
        };
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fp>,
    ) -> Result<(), Error> {
        let test_chip = TestChip::construct(config.tconf);
        let bchip = ByteOpChip::<Fp, Fq, ShiftOp>::construct(config.bconf);
        let dchip = DecomposeChip::<Fp>::constructor(config.dconf.clone());
        let pchip = PlusChip::<Fp>::construct(config.pconf);
        dchip.load_range_table(&mut layouter)?;
        bchip.alloc_table(
            layouter.namespace(|| "shift tbl"),
            L_RANGE,
            R_RANGE,
            S_RANGE,
        )?;

        let dchip_dup = DecomposeChip::<Fp>::constructor(config.dconf);
        let nchip = FNormChip::<Fq, Fp>::construct(config.nconf, dchip_dup);
        let schip = ShortMultChip::<Fq, Fp>::construct(config.sconf);
        let mchip = FMultChip::<Fq, Fp>::construct(config.mconf, schip, dchip, pchip, nchip);

        let x0 = test_chip.load_private(layouter.namespace(|| "load"), Some(self.inputs[0]))?;
        let x1 = test_chip.load_private(layouter.namespace(|| "load"), Some(self.inputs[1]))?;
        let x2 = test_chip.load_private(layouter.namespace(|| "load"), Some(self.inputs[2]))?;
        let y0 = test_chip.load_private(layouter.namespace(|| "load"), Some(self.inputs[3]))?;
        let y1 = test_chip.load_private(layouter.namespace(|| "load"), Some(self.inputs[4]))?;
        let y2 = test_chip.load_private(layouter.namespace(|| "load"), Some(self.inputs[5]))?;

        let out = mchip.mult(
            &mut layouter,
            Fs::<Fp> {
                values: [
                    Number::<Fp> {
                        cell: x0.cell,
                        value: Some(self.inputs[0]),
                    },
                    Number::<Fp> {
                        cell: x1.cell,
                        value: Some(self.inputs[1]),
                    },
                    Number::<Fp> {
                        cell: x2.cell,
                        value: Some(self.inputs[2]),
                    },
                ],
            },
            Fs::<Fp> {
                values: [
                    Number::<Fp> {
                        cell: y0.cell,
                        value: Some(self.inputs[3]),
                    },
                    Number::<Fp> {
                        cell: y1.cell,
                        value: Some(self.inputs[4]),
                    },
                    Number::<Fp> {
                        cell: y2.cell,
                        value: Some(self.inputs[5]),
                    },
                ],
            },
        )?;

        println!("values = {:?}", out.values);

        test_chip.expose_public(layouter.namespace(|| "out0"), out.values[0].clone(), 0)?;
        test_chip.expose_public(layouter.namespace(|| "out1"), out.values[1].clone(), 1)?;
        test_chip.expose_public(layouter.namespace(|| "out2"), out.values[2].clone(), 2)?;
        Ok(())
    }
}
// ANCHOR_END: circuit

#[test]
fn test1() {
    use halo2::{dev::MockProver, pasta::Fp};
    let k = 17;

    // let input = Some(Fp::from(400)); // 256 + 144
    let inputs = [
        Fp::from(1),
        Fp::from(2),
        Fp::from(3),
        Fp::from(1),
        Fp::from(2),
        Fp::from(3),
    ];

    let circuit = MyCircuit { inputs };

    let mut public_inputs = vec![
        Fp::from_u128(0x00000000000000000000000000000000000000000000a8b98c46eb2100000002),
        Fp::from_u128(0x00000000000000000000000000000000000000000000a71840d8684d88580998),
        Fp::from_u128(0x0000000000000000000000000000000000000000400bfffffffffffb2e127c98),
    ];

    let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
    assert_eq!(prover.verify(), Ok(()));

    public_inputs[0] += Fp::one();
    let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();
    assert!(prover.verify().is_err());
}

#[test]
fn fmult_test2() {
    use halo2::{dev::MockProver, pasta::Fp};
    let k = 17;

    // let input = Some(Fp::from(400)); // 256 + 144
    let inputs = [
        Fp::from(1),
        Fp::from(2),
        Fp::from(0),
        Fp::from(1),
        Fp::from(2),
        Fp::from(0),
    ];

    let circuit = MyCircuit { inputs };

    let mut public_inputs = vec![Fp::from_u128(1), Fp::from_u128(4), Fp::from_u128(4)];

    let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
    assert_eq!(prover.verify(), Ok(()));

    public_inputs[0] += Fp::one();
    let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();
    assert!(prover.verify().is_err());
}

#[test]
fn fmult_test3() {
    use halo2::{dev::MockProver, pasta::Fp};
    let k = 17;

    let a0 = Fp::from_u128(0x123456789abd98761234);
    let a1 = Fp::from_u128(0x23243242543254355434);
    let a2 = Fp::from_u128(0x1232349984344444421234);
    let b0 = Fp::from_u128(0x47839127448391247834);
    let b1 = Fp::from_u128(0x47381947832947923474);
    let b2 = Fp::from_u128(0x8797923472384247847238);
    let c0 = Fp::from_u128(0xed2a617aefbf7587e5be);
    let c1 = Fp::from_u128(0x244d54126c138463f7f4);
    let c2 = Fp::from_u128(0x84254c2b15f38e64597d0dfec);

    let inputs = [a0, a1, a2, b0, b1, b2];

    let circuit = MyCircuit { inputs };

    let mut public_inputs = vec![c0, c1, c2];

    let merge = |x0: Fp, x1: Fp, x2: Fp| {
        Fq::from_bytes(&x0.to_bytes()).unwrap()
            + Fq::from_bytes(&x1.to_bytes()).unwrap() * Fq::from(2).pow(&[80u64, 0u64, 0u64, 0u64])
            + Fq::from_bytes(&x2.to_bytes()).unwrap() * Fq::from(2).pow(&[160u64, 0u64, 0u64, 0u64])
    };

    assert_eq!(merge(a0, a1, a2) * merge(b0, b1, b2), merge(c0, c1, c2));

    let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
    assert_eq!(prover.verify(), Ok(()));

    public_inputs[0] += Fp::one();
    let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();
    assert!(prover.verify().is_err());
}

#[test]
fn test3() {
    use halo2::{dev::MockProver, pasta::Fp};
    let k = 17;

    // let input = Some(Fp::from(400)); // 256 + 144
    let inputs = [
        Fp::from(0),
        Fp::from(0),
        Fp::from(3),
        Fp::from(0),
        Fp::from(0),
        Fp::from(3),
    ];

    let circuit = MyCircuit { inputs };

    let mut public_inputs = vec![
        Fp::from_u128(796780324800677309054977),
        Fp::from_u128(789082597096295386057108),
        Fp::from_u128(0x3ffffffffffffffb2e127c8e),
    ];

    let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
    assert_eq!(prover.verify(), Ok(()));

    public_inputs[0] += Fp::one();
    let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();
    assert!(prover.verify().is_err());
}


