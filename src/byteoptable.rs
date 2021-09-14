use halo2::{
    pasta::{Fp, Fq},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, TableColumn},
    poly::Rotation,
};

use halo2::arithmetic::FieldExt;
use halo2::circuit::{Chip, Layouter, SimpleFloorPlanner};

use std::marker::PhantomData;

use crate::types::Number;
use crate::utils::proj_f;

pub trait ByteOp<F: FieldExt> {
    fn bop(op1: usize, op2: usize) -> F;
}

pub struct ByteOpChip<Fr: FieldExt, Fp: FieldExt, B: ByteOp<Fp>> {
    config: ByteOpChipConfig,
    _marker_fr: PhantomData<Fr>,
    _marker_fp: PhantomData<Fp>,
    _marker_b: PhantomData<B>,
}

#[derive(Clone, Debug)]
pub struct ByteOpChipConfig {
    l_col: Column<Advice>,
    r_col: Column<Advice>,
    o_col: Column<Advice>,
    s_col: Column<Advice>,

    pub tbl_l: TableColumn,
    pub tbl_r: TableColumn,
    pub tbl_o: TableColumn,
    pub tbl_s: TableColumn,
}

impl<Fr: FieldExt, Fp: FieldExt, B: ByteOp<Fp>> Chip<Fr> for ByteOpChip<Fr, Fp, B> {
    type Config = ByteOpChipConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<Fr: FieldExt, Fp: FieldExt, B: ByteOp<Fp>> ByteOpChip<Fr, Fp, B> {
    pub fn construct(config: ByteOpChipConfig) -> Self {
        ByteOpChip {
            config,
            _marker_fr: PhantomData,
            _marker_fp: PhantomData,
            _marker_b: PhantomData,
        }
    }

    pub fn configure(cs: &mut ConstraintSystem<Fr>) -> ByteOpChipConfig {
        let l_col = cs.advice_column();
        let r_col = cs.advice_column();
        let o_col = cs.advice_column();
        let s_col = cs.advice_column();

        cs.enable_equality(l_col.into());
        cs.enable_equality(r_col.into());
        cs.enable_equality(o_col.into());
        cs.enable_equality(s_col.into());

        let tbl_l = cs.lookup_table_column();
        let tbl_r = cs.lookup_table_column();
        let tbl_o = cs.lookup_table_column();
        let tbl_s = cs.lookup_table_column();

        cs.lookup(|meta| {
            let l_cur = meta.query_advice(l_col, Rotation::cur());
            let r_cur = meta.query_advice(r_col, Rotation::cur());
            let o_cur = meta.query_advice(o_col, Rotation::cur());
            let s_cur = meta.query_advice(s_col, Rotation::cur());
            vec![
                (l_cur, tbl_l),
                (r_cur, tbl_r),
                (o_cur, tbl_o),
                (s_cur, tbl_s),
            ]
        });

        ByteOpChipConfig {
            l_col,
            r_col,
            o_col,
            s_col,
            tbl_l,
            tbl_r,
            tbl_o,
            tbl_s,
        }
    }

    pub fn alloc_table(
        &self,
        mut layouter: impl Layouter<Fr>,
        lrange: usize,
        rrange: usize,
        srange: usize,
    ) -> Result<(), Error> {
        layouter.assign_table(
            || "shift-table",
            |mut table| {
                for l in 0..lrange {
                    for r in 0..rrange {
                        for s in 0..srange {
                            let offset = l * R_RANGE * S_RANGE + r * S_RANGE + s;
                            let v = B::bop(l, r);
                            //println!("l: {}, r: {} s:{} o:{:?}", l, r, s, repr.proj::<Fr>(s));

                            table.assign_cell(
                                || "table_idx",
                                self.config.tbl_o,
                                offset,
                                || Ok(proj_f::<Fp, Fr>(v, s)),
                            )?;

                            table.assign_cell(
                                || "table_idx",
                                self.config.tbl_l,
                                offset,
                                || Ok(Fr::from_u64(l as u64)),
                            )?;

                            table.assign_cell(
                                || "table_idx",
                                self.config.tbl_r,
                                offset,
                                || Ok(Fr::from_u64(r as u64)),
                            )?;
                            table.assign_cell(
                                || "table_idx",
                                self.config.tbl_s,
                                offset,
                                || Ok(Fr::from_u64(s as u64)),
                            )?;
                        }
                    }
                }
                Ok(())
            },
        )
    }

    fn constrain(
        &self,
        layouter: &mut impl Layouter<Fr>,
        ol: Number<Fr>,
        or: Number<Fr>,
        os: Number<Fr>,
        oo: Number<Fr>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "private and public inputs",
            |mut region| {
                let l = region.assign_advice(
                    || "private input `l`",
                    self.config.l_col,
                    0,
                    || ol.value.ok_or(Error::SynthesisError),
                )?;
                let r = region.assign_advice(
                    || "private input `r`",
                    self.config.r_col,
                    0,
                    || or.value.ok_or(Error::SynthesisError),
                )?;
                let s = region.assign_advice(
                    || "private input `s`",
                    self.config.s_col,
                    0,
                    || os.value.ok_or(Error::SynthesisError),
                )?;
                let o = region.assign_advice(
                    || "private input `v`",
                    self.config.o_col,
                    0,
                    || oo.value.ok_or(Error::SynthesisError),
                )?;
                region.constrain_equal(ol.cell, l)?;
                println!("{:?}", ol.cell);
                println!("{:?}", l);
                region.constrain_equal(or.cell, r)?;
                region.constrain_equal(os.cell, s)?;
                region.constrain_equal(oo.cell, o)?;
                Ok(())
            },
        )
    }
}

#[derive(Clone, Default)]
struct ByteOpCircuit {
    // Private inputs.
    l: Option<Fp>,
    r: Option<Fp>,
    s: Option<Fp>,

    // Public input (from prover).
    o: Option<Fp>,
}

const CHUNCK_BITS: usize = 8;
const L_RANGE: usize = 1 << CHUNCK_BITS;
const R_RANGE: usize = 256 * 2 / CHUNCK_BITS;
const S_RANGE: usize = 3;

pub struct ShiftOp {
    m: PhantomData<()>,
}

impl ByteOp<Fq> for ShiftOp {
    fn bop(x: usize, y: usize) -> Fq {
        let mut times = (y as u64) * (CHUNCK_BITS as u64) + 240;
        let mut curr = Fq::from_u64(2u64);
        let mut acc = Fq::from_u64(x as u64);
        while times > 0 {
            if times & 1 == 1 {
                acc = acc * curr;
            }
            curr = curr * curr;
            times >>= 1;
        }
        return acc;
    }
}

pub type ShiftOpChip<Fp> = ByteOpChip<Fp, Fq, ShiftOp>;

use crate::testchip::*;

#[derive(Clone, Debug)]
pub struct CircuitConfig {
    bopc: ByteOpChipConfig,
    testc: TestConfig,
}

impl Circuit<Fp> for ByteOpCircuit {
    type Config = CircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(cs: &mut ConstraintSystem<Fp>) -> Self::Config {
        let bopc = ByteOpChip::<Fp, Fq, ShiftOp>::configure(cs);
        let testc = TestChip::configure(cs);
        return CircuitConfig { bopc, testc };
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fp>,
    ) -> Result<(), Error> {
        let test_chip = TestChip::construct(config.testc);
        let l = test_chip.load_private(layouter.namespace(|| "load l"), self.l)?;
        let r = test_chip.load_private(layouter.namespace(|| "load r"), self.r)?;
        let s = test_chip.load_private(layouter.namespace(|| "load s"), self.s)?;
        let o = test_chip.load_private(layouter.namespace(|| "load o"), self.o)?;

        let op_chip = ByteOpChip::<Fp, Fq, ShiftOp>::construct(config.bopc);
        op_chip.alloc_table(layouter.namespace(|| "shift tbl"), L_RANGE, R_RANGE, S_RANGE)?;
        op_chip.constrain(&mut layouter, l, r, s, o)?;
        Ok(())
    }
}

#[test]
fn circuit1() {
    use halo2::dev::{MockProver};

    let circuit = ByteOpCircuit {
        l: Some(Fp::from(255)),
        r: Some(Fp::from(59)),
        s: Some(Fp::from(1)),
        o: Some(Fp::from_u128(204053304434175565874536u128)),
    };
    let ret = vec![Fp::from_u128(204053304434175565874536u128)];
    let prover = MockProver::run(17, &circuit, vec![ret]).unwrap();
    let presult = prover.verify();

    assert!(presult.is_ok());
}

#[test]
fn circuit2() {
    use halo2::dev::{MockProver};

    let circuit = ByteOpCircuit {
        l: Some(Fp::from(0)),
        r: Some(Fp::from(0)),
        s: Some(Fp::from(0)),
        o: Some(Fp::from_u128(0)),
    };
    let ret = vec![Fp::from_u128(0)];
    let prover = MockProver::run(17, &circuit, vec![ret]).unwrap();
    let presult = prover.verify();

    assert!(presult.is_ok());
}
