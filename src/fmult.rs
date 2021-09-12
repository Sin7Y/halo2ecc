use halo2::{
    arithmetic::FieldExt,
    circuit::{Chip, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};

use num_bigint::BigUint;

use crate::types::{Fs, FsAdvice, Number};
use crate::utils::*;

use std::convert::TryInto;
use std::marker::PhantomData;

trait FMult<Fp: FieldExt, F: FieldExt>: Chip<F> {
    fn mult(&self, layouter: &mut impl Layouter<F>, a: Fs<F>, b: Fs<F>) -> Result<Fs<F>, Error>;
}

struct FMultChip<Fp: FieldExt, F: FieldExt> {
    config: FMultConfig<F>,
    _marker: PhantomData<F>,
    __marker: PhantomData<Fp>,
}

#[derive(Clone, Debug)]
struct FMultConfig<F: FieldExt> {
    /// x * y = d * p + r
    x: FsAdvice<F>,
    y: FsAdvice<F>,

    /// r's limbs should be in range [96, 80, 80]
    r: FsAdvice<F>,

    // d should be less than Fp
    d: FsAdvice<F>,

    /// ol = x * y
    /// or = d * p + r
    /// 'ol' should be equal to 'or' after normalize
    ol: [Column<Advice>; 4],
    or: [Column<Advice>; 4],

    /// support x * y = t0 + (t1 << 160) + (t2 << 240) + (t3 << 320)
    /// t0 < 160bits, t1 < 80bits, t2 < 80bits
    /// cl0 < 96bits
    /// cl1 < 112bits
    /// cl2 < 112bits
    ///
    /// ol0 = t0 + (cl0 << 160)
    /// ol1 + cl0 = t1 + (cl1 << 80)
    /// ol2 + cl1 = t2 + (cl2 << 80)
    /// ol2 + cl1 = t3
    /// same to or.
    /// omit t3 because we can just constrain on ol2 + cl1 = or2 + cr1
    cl: [Column<Advice>; 3],
    cr: [Column<Advice>; 3],
    t: [Column<Advice>; 3],

    sel: Selector,
    // for intermediate var
    // advice: Column<Advice>,
}

impl<Fp: FieldExt, F: FieldExt> FMultChip<Fp, F> {
    fn construct(config: <Self as Chip<F>>::Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
            __marker: PhantomData,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> FMultConfig<F> {
        let s80 = pow2::<F>(80);
        let shift_80 = Expression::Constant(s80);
        let shift_160 = Expression::Constant(s80 * s80);

        let sel = meta.selector();

        let x = advice_fs_column(meta);
        let y = advice_fs_column(meta);
        let r = advice_fs_column(meta);
        let d = advice_fs_column(meta);

        for i in 0..3 {
            meta.enable_equality(x.advices[i].into());
            meta.enable_equality(y.advices[i].into());
        }

        let ol = [
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
        ];

        let or = [
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
        ];

        let cl = [
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
        ];

        let cr = [
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
        ];

        let t = [
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
        ];

        for i in 0..3 {
            meta.enable_equality(r.advices[i].into());
            meta.enable_equality(d.advices[i].into());
            meta.enable_equality(cr[i].into());
            meta.enable_equality(cl[i].into());
            meta.enable_equality(t[i].into());
        }

        for i in 0..4 {
            meta.enable_equality(ol[i].into());
            meta.enable_equality(or[i].into());
        }

        meta.create_gate("fmult-l", |meta| {
            let s = meta.query_selector(sel);
            // Controlled by init_sel
            // | x | y | ol |

            let xh = meta.query_advice(x.advices[2], Rotation::cur());
            let xm = meta.query_advice(x.advices[1], Rotation::cur());
            let xl = meta.query_advice(x.advices[0], Rotation::cur());
            let yh = meta.query_advice(y.advices[2], Rotation::cur());
            let ym = meta.query_advice(y.advices[1], Rotation::cur());
            let yl = meta.query_advice(y.advices[0], Rotation::cur());
            let o3 = meta.query_advice(ol[3], Rotation::cur());
            let o2 = meta.query_advice(ol[2], Rotation::cur());
            let o1 = meta.query_advice(ol[1], Rotation::cur());
            let o0 = meta.query_advice(ol[0], Rotation::cur());

            vec![
                s.clone()
                    * (o0
                        - (xl.clone() * yl.clone()
                            + (xm.clone() * yl.clone() + xl.clone() * ym.clone())
                                * shift_80.clone())),
                s.clone()
                    * (o1
                        - (xm.clone() * ym.clone()
                            + xh.clone() * yl.clone()
                            + xl.clone() * yh.clone())),
                s.clone() * (o2 - (xm.clone() * yh.clone() + xh.clone() * ym.clone())),
                s.clone() * (o3 - (xh.clone() * yh.clone())),
            ]
        });

        meta.create_gate("fmult-r", |meta| {
            let s = meta.query_selector(sel);
            // Controlled by init_sel
            // | d | r | or

            let dh = meta.query_advice(d.advices[2], Rotation::cur());
            let dm = meta.query_advice(d.advices[1], Rotation::cur());
            let dl = meta.query_advice(d.advices[0], Rotation::cur());
            let rh = meta.query_advice(r.advices[2], Rotation::cur());
            let rm = meta.query_advice(r.advices[1], Rotation::cur());
            let rl = meta.query_advice(r.advices[0], Rotation::cur());
            let o3 = meta.query_advice(or[3], Rotation::cur());
            let o2 = meta.query_advice(or[2], Rotation::cur());
            let o1 = meta.query_advice(or[1], Rotation::cur());
            let o0 = meta.query_advice(or[0], Rotation::cur());

            let p = fp_modulus_on_fr::<Fp, F>();
            let pl = Expression::Constant(p[0]);
            let pm = Expression::Constant(p[1]);
            let ph = Expression::Constant(p[2]);

            vec![
                s.clone()
                    * (o0
                        - (pl.clone() * dl.clone()
                            + shift_80.clone()
                                * (pm.clone() * dl.clone() + pl.clone() * dm.clone() + rm)
                            + rl)),
                s.clone()
                    * (o1
                        - (pm.clone() * dm.clone()
                            + ph.clone() * dl.clone()
                            + pl.clone() * dh.clone()
                            + rh)),
                s.clone() * (o2 - (pm.clone() * dh.clone() + ph.clone() * dm.clone())),
                s.clone() * (o3 - (ph.clone() * dh.clone())),
            ]
        });

        meta.create_gate("fmult-equal", |meta| {
            let s = meta.query_selector(sel);
            // Controlled by init_sel
            // | ol | cl | or | cr | t
            let mut ol_curr = vec![];
            let mut or_curr = vec![];
            let mut cl_curr = vec![];
            let mut cr_curr = vec![];
            let mut t_curr = vec![];

            for i in 0..3 {
                cl_curr.push(meta.query_advice(cl[i], Rotation::cur()));
                cr_curr.push(meta.query_advice(cr[i], Rotation::cur()));
                t_curr.push(meta.query_advice(t[i], Rotation::cur()));
            }

            for i in 0..4 {
                ol_curr.push(meta.query_advice(ol[i], Rotation::cur()));
                or_curr.push(meta.query_advice(or[i], Rotation::cur()));
            }

            vec![
                s.clone()
                    * (ol_curr[0].clone()
                        - t_curr[0].clone()
                        - cl_curr[0].clone() * shift_160.clone()),
                s.clone()
                    * (ol_curr[1].clone() + cl_curr[0].clone()
                        - t_curr[1].clone()
                        - cl_curr[1].clone() * shift_80.clone()),
                s.clone()
                    * (ol_curr[2].clone() + cl_curr[1].clone()
                        - t_curr[2].clone()
                        - cl_curr[2].clone() * shift_80.clone()),
                s.clone()
                    * (or_curr[0].clone()
                        - t_curr[0].clone()
                        - cr_curr[0].clone() * shift_160.clone()),
                s.clone()
                    * (or_curr[1].clone() + cr_curr[0].clone()
                        - t_curr[1].clone()
                        - cr_curr[1].clone() * shift_80.clone()),
                s.clone()
                    * (or_curr[2].clone() + cr_curr[1].clone()
                        - t_curr[2].clone()
                        - cr_curr[2].clone() * shift_80.clone()),
                s.clone()
                    * (ol_curr[3].clone() + cl_curr[2].clone()
                        - or_curr[3].clone()
                        - cr_curr[2].clone()),
            ]
        });

        return FMultConfig {
            x,
            y,
            r,
            d,
            ol,
            or,
            cl,
            cr,
            t,
            sel,
        };
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
    fn mul(
        &self,
        layouter: &mut impl Layouter<F>,
        in_x: Fs<F>,
        in_y: Fs<F>,
    ) -> Result<Fs<F>, Error> {
        let config = self.config();

        let mut out_r = None;
        let mut out_d = None;
        let mut out_ol = vec![];
        let mut out_or = vec![];
        let mut out_cl = vec![];
        let mut out_cr = vec![];
        let mut out_t = vec![];

        // 1. Assign top-level gates.
        layouter.assign_region(
            || "fmult",
            |mut region| {
                let x = in_x
                    .values
                    .iter()
                    .map(|ix| ix.value.unwrap())
                    .collect::<Vec<F>>()
                    .try_into()
                    .unwrap();
                let y = in_y
                    .values
                    .iter()
                    .map(|iy| iy.value.unwrap())
                    .collect::<Vec<F>>()
                    .try_into()
                    .unwrap();

                let x_bigunit = fp_on_fr_to_big_uint::<F>(x);
                let y_bigunit = fp_on_fr_to_big_uint::<F>(y);
                let xy_bigunit = x_bigunit * y_bigunit;
                let p_bigunit = fp_modulus_on_big_uint::<Fp>();

                let r = fp_on_fr_from_big_unit::<F>(xy_bigunit.clone() % p_bigunit.clone());
                let d = fp_on_fr_from_big_unit::<F>(xy_bigunit.clone() / p_bigunit.clone());
                let p = fp_modulus_on_fr::<Fp, F>();
                let ol = fp_on_fr_mul_plus(x, y, [F::zero(); 3]);
                let or = fp_on_fr_mul_plus(p, d, r);

                let shift_80 = BigUint::from(2u64).pow(160);
                let shift_160 = shift_80.clone() * shift_80.clone();

                let carry_of_f4 = |o: &[F; 4]| -> ([F; 3], [F; 3]) {
                    let mut carry = vec![];
                    let mut rem = vec![];

                    carry.push(big_unit_from_f(o[0]) / shift_160.clone());
                    carry.push((carry[0].clone() + big_unit_from_f(o[1])) / shift_80.clone());
                    carry.push((carry[1].clone() + big_unit_from_f(o[2])) / shift_80.clone());

                    rem.push(big_unit_from_f(o[0]) % shift_160.clone());
                    rem.push((carry[0].clone() + big_unit_from_f(o[1])) % shift_80.clone());
                    rem.push((carry[1].clone() + big_unit_from_f(o[2])) % shift_80.clone());

                    return (
                        carry
                            .iter()
                            .map(|x| f_from_big_unit(x))
                            .collect::<Vec<_>>()
                            .try_into()
                            .unwrap(),
                        rem.iter()
                            .map(|x| f_from_big_unit(x))
                            .collect::<Vec<_>>()
                            .try_into()
                            .unwrap(),
                    );
                };

                let (cl, t) = carry_of_f4(&ol);
                let (cr, _) = carry_of_f4(&or);

                assign_fs(&mut region, config.x, &in_x, 0, "x")?;
                assign_fs(&mut region, config.y, &in_y, 0, "y")?;

                out_r = Some(assign_fp(&mut region, config.r, r, 0, "r"));
                out_d = Some(assign_fp(&mut region, config.d, d, 0, "d"));

                for i in 0..4 {
                    let value = ol[i];
                    let cell = region.assign_advice(|| "ol", config.ol[i], 0, || Ok(value))?;
                    out_ol.push(cell);

                    let value = or[i];
                    let cell = region.assign_advice(|| "or", config.or[i], 0, || Ok(value))?;
                    out_or.push(cell);
                }

                for i in 0..3 {
                    let value = cl[i];
                    let cell = region.assign_advice(|| "cl", config.cl[i], 0, || Ok(value))?;
                    out_cl.push(cell);

                    let value = cr[i];
                    let cell = region.assign_advice(|| "cr", config.cr[i], 0, || Ok(value))?;
                    out_cr.push(cell);

                    let value = t[i];
                    let cell = region.assign_advice(|| "t", config.t[i], 0, || Ok(value))?;
                    out_t.push(cell);
                }

                Ok(())
            },
        )?;

        // 2. check range of r and d cl cr ct

        // prange_check(r) // 32

        // 16bit width
        // range_check(d[0], 5)
        // range_check(d[1], 5)
        // range_check(d[2], 6)

        // range_check(cl[0], 3)
        // range_check(cl[1], 4)
        // range_check(cl[2], 4)

        // range_check(cr[0], 3)
        // range_check(cr[1], 4)
        // range_check(cr[2], 4)

        // range_check(t[0], 10)
        // range_check(t[1], 5)
        // range_check(t[2], 5)

        return Ok(out_r.unwrap());
    }
}

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
    tconf: TestConfig,
    mconf: FMultConfig<Fp>,
}

impl Circuit<Fp> for MyCircuit {
    // Since we are using a single chip for everything, we can just reuse its config.
    type Config = CircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }
    fn configure(cs: &mut ConstraintSystem<Fp>) -> Self::Config {
        let mconf = FMultChip::<Fq, Fp>::configure(cs);
        let tconf = TestChip::configure(cs);
        return CircuitConfig { tconf, mconf };
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fp>,
    ) -> Result<(), Error> {
        let test_chip = TestChip::construct(config.tconf);
        let mchip = FMultChip::<Fq, Fp>::construct(config.mconf);

        let x0 = test_chip.load_private(layouter.namespace(|| "load"), Some(self.inputs[0]))?;
        let x1 = test_chip.load_private(layouter.namespace(|| "load"), Some(self.inputs[1]))?;
        let x2 = test_chip.load_private(layouter.namespace(|| "load"), Some(self.inputs[2]))?;
        let y0 = test_chip.load_private(layouter.namespace(|| "load"), Some(self.inputs[3]))?;
        let y1 = test_chip.load_private(layouter.namespace(|| "load"), Some(self.inputs[4]))?;
        let y2 = test_chip.load_private(layouter.namespace(|| "load"), Some(self.inputs[5]))?;

        let out = mchip.mul(
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

#[test]
fn fmult_test() {
    use halo2::{dev::MockProver, pasta::Fp};
    let k = 17;

    let a0 = Fp::from_u128(0x123456789abd98761234);
    let a1 = Fp::from_u128(0x23243242543254355434);
    let a2 = Fp::from_u128(0x1232349984344444421234);
    let b0 = Fp::from_u128(0x47839127448391247834);
    let b1 = Fp::from_u128(0x47381947832947923474);
    let b2 = Fp::from_u128(0x8797923472384247847238);
    let c0 = Fp::from_u128(0x289b4c56a07e7587e59d);
    let c1 = Fp::from_u128(0x244d540e00f9cbe6bbcb);
    let c2 = Fp::from_u128(0x0254c2b15f38e64597d0dfec);

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
