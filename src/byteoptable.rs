use halo2::{
    dev::{MockProver, VerifyFailure},
    pasta::{Fp, Fq},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, TableColumn},
    poly::Rotation,
};

use halo2::arithmetic::FieldExt;
use halo2::circuit::{Chip, Layouter, SimpleFloorPlanner};

use num_bigint::BigUint;
use std::convert::TryInto;
use std::marker::PhantomData;

trait ByteOp<F: FieldExt> {
    fn bop(op1: usize, op2: usize) -> F;
}

struct FpRepr<Fp: FieldExt> {
    value: Fp,
}

impl<Fp: FieldExt> FpRepr<Fp> {
    fn proj<Fr: FieldExt>(&self, i: usize) -> Fr {
        if i > 2 {
            return Fr::from(0);
        } else if i == 2 {
            return Fr::from_bytes(
                &[&self.value.to_bytes()[20..32], &[0u8; 20][..]]
                    .concat()
                    .try_into()
                    .unwrap(),
            )
            .unwrap();
        } else if i == 1 {
            return Fr::from_bytes(
                &[&self.value.to_bytes()[10..20], &[0u8; 22][..]]
                    .concat()
                    .try_into()
                    .unwrap(),
            )
            .unwrap();
        } else {
            return Fr::from_bytes(
                &[&self.value.to_bytes()[0..10], &[0u8; 22][..]]
                    .concat()
                    .try_into()
                    .unwrap(),
            )
            .unwrap();
        }
    }

    fn get_op_entry<B: ByteOp<Fp>>(x: usize, y: usize) -> FpRepr<Fp> {
        FpRepr {
            value: B::bop(x, y),
        }
    }
}

struct ByteOpChip<Fr: FieldExt, Fp: FieldExt, B: ByteOp<Fp>> {
    config: ByteOpChipConfig,
    _marker_fr: PhantomData<Fr>,
    _marker_fp: PhantomData<Fp>,
    _marker_b: PhantomData<B>,
}

#[derive(Clone, Debug)]
struct ByteOpChipConfig {
    l_col: Column<Advice>,
    r_col: Column<Advice>,
    o_col: Column<Advice>,
    s_col: Column<Advice>,

    tbl_l: TableColumn,
    tbl_r: TableColumn,
    tbl_o: TableColumn,
    tbl_s: TableColumn,
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
    fn new(config: ByteOpChipConfig) -> Self {
        ByteOpChip {
            config,
            _marker_fr: PhantomData,
            _marker_fp: PhantomData,
            _marker_b: PhantomData,
        }
    }

    fn configure(cs: &mut ConstraintSystem<Fr>) -> ByteOpChipConfig {
        let l_col = cs.advice_column();
        let r_col = cs.advice_column();
        let o_col = cs.advice_column();
        let s_col = cs.advice_column();

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

    fn alloc_table(
        &self,
        layouter: &mut impl Layouter<Fr>,
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
                            let repr = FpRepr::<Fp>::get_op_entry::<B>(l, r);
                            //println!("l: {}, r: {} s:{} o:{:?}", l, r, s, repr.proj::<Fr>(s));

                            table.assign_cell(
                                || "table_idx",
                                self.config.tbl_o,
                                offset,
                                || Ok(repr.proj::<Fr>(s)),
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

    fn alloc_private_and_public_inputs(
        &self,
        layouter: &mut impl Layouter<Fr>,
        ol: Option<Fr>,
        or: Option<Fr>,
        os: Option<Fr>,
        oo: Option<Fr>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "private and public inputs",
            |mut region| {
                region.assign_advice(
                    || "private input `l`",
                    self.config.l_col,
                    0,
                    || ol.ok_or(Error::SynthesisError),
                )?;
                region.assign_advice(
                    || "private input `r`",
                    self.config.r_col,
                    0,
                    || or.ok_or(Error::SynthesisError),
                )?;
                region.assign_advice(
                    || "private input `s`",
                    self.config.s_col,
                    0,
                    || os.ok_or(Error::SynthesisError),
                )?;
                region.assign_advice(
                    || "private input `v`",
                    self.config.o_col,
                    0,
                    || oo.ok_or(Error::SynthesisError),
                )?;
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

struct ShiftOp {
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

impl Circuit<Fp> for ByteOpCircuit {
    type Config = ByteOpChipConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(cs: &mut ConstraintSystem<Fp>) -> Self::Config {
        ByteOpChip::<Fp, Fq, ShiftOp>::configure(cs)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fp>,
    ) -> Result<(), Error> {
        let op_chip = ByteOpChip::<Fp, Fq, ShiftOp>::new(config);
        op_chip.alloc_table(&mut layouter, L_RANGE, R_RANGE, S_RANGE)?;
        op_chip.alloc_private_and_public_inputs(&mut layouter, self.l, self.r, self.s, self.o)?;
        Ok(())
    }
}

#[test]
fn circuit() {
    // The number of rows used in the constraint system matrix.
    const N_ROWS_USED: u32 = 256;

    // The row index for the public input.
    const PUB_INPUT_ROW: usize = 0;

    // The verifier's public input.
    const PUB_INPUT: u64 = 3;

    // The actual number of rows in the constraint system is `2^k` where `N_ROWS_USED <= 2^k`.
    let k = (N_ROWS_USED as f32).log2().ceil() as u32;
    println!("k is {}", k);

    let mut pub_inputs = vec![Fp::zero()];
    pub_inputs[PUB_INPUT_ROW] = Fp::from(PUB_INPUT);

    /*
    let circuit = ByteOpCircuit {
        l: Some(Fp::from(123)),
        r: Some(Fp::from(10)),
        s: Some(Fp::from(1)),
        o: Some(Fp::from_u128(709746996383430097242516u128)),
    };
    */

        let circuit = ByteOpCircuit {
            l: Some(Fp::from(255)),
            r: Some(Fp::from(59)),
            s: Some(Fp::from(1)),
            o: Some(Fp::from_u128(204053304434175565874536u128)),
        };
    let prover = MockProver::run(17, &circuit, vec![]).unwrap();
    let presult = prover.verify();
    println!("Error {:?}", presult);

    assert!(presult.is_ok());

    // Assert that the public input gate is unsatisfied when `c != PUB_INPUT` (but when the lookup
    // passes).
    /*
    let bad_circuit = ByteOpCircuit {
        a: Some(Fp::from(2)),
        b: Some(Fp::from(3)),
        c: Some(Fp::from(2)),
    };
    let prover = MockProver::run(k, &bad_circuit, vec![pub_inputs.clone()]).unwrap();
    match prover.verify() {
        Err(errors) => {
            assert_eq!(errors.len(), 1, "expected one verification error, found: {:?}", errors);
            match &errors[0] {
                VerifyFailure::Gate { .. } => {}
                e => panic!("expected 'public input' gate error, found: {:?}", e),
            };
        }
        _ => panic!("expected `prover.verify()` to fail"),
    };

    // Assert that the lookup fails when `(a, b, c)` is not a row in the table; the lookup table is
    // for 2-bit BYTE, using a 3-bit BYTE input `a = 4` should result in a lookup failure.
    let mut bad_circuit = circuit.clone();
    bad_circuit.a = Some(Fp::from(4));
    let prover = MockProver::run(k, &bad_circuit, vec![pub_inputs]).unwrap();
    match prover.verify() {
        Err(errors) => {
            assert_eq!(errors.len(), 1, "expected one verification error");
            match &errors[0] {
                VerifyFailure::Lookup { .. } => {}
                e => panic!("expected lookup error, found: {:?}", e),
            };
        }
        _ => panic!("expected `prover.verify()` to fail"),
    };
    */
}
