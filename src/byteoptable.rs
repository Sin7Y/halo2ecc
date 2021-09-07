use halo2::{
    dev::{MockProver, VerifyFailure},
    pasta::Fp,
    plonk::{Advice, Assignment, Circuit, Column, ConstraintSystem, Error, Fixed, Selector, TableColumn},
    poly::Rotation,
};

use halo2::circuit::{Region, Cell, Chip, Layouter, SimpleFloorPlanner};
use halo2::arithmetic::FieldExt;

use num_bigint::BigUint;
use std::marker::PhantomData;

trait ByteOp {
    fn bop(op1: BigUint, op2: BigUint) -> BigUint;
}

struct FpRepr<B: ByteOp> {
    values: Vec<u8>,
    _marker: PhantomData<B>,
}

impl<B: ByteOp> FpRepr<B> {
    fn proj(&self, i:usize) -> u8 {
        if(i >= self.values.len()) {
            return 0;
        } else {
            return self.values[i];
        }
    }
    fn repr (&self) -> BigUint {
        BigUint::from_bytes_le(&self.values)
    }
    fn get_op_entry (seg_x:BigUint, seg_y:BigUint, basis: u32) -> FpRepr<B> {
        FpRepr {
            values: (B::bop (seg_x, seg_y) << basis).to_bytes_le(),
            _marker: PhantomData,
        }
    }
}

const BYTE_BITS: usize = 8;

struct ByteOpChip<F: FieldExt, B:ByteOp> {
    config: ByteOpChipConfig,
    _marker_f: PhantomData<F>,
    _marker_b: PhantomData<B>,
}

#[derive(Clone, Debug)]
struct ByteOpChipConfig {
    l_col: Column<Advice>,
    r_col: Column<Advice>,
    o_col: Column<Advice>,
    tbl_o: TableColumn,
    tbl_l: TableColumn,
    tbl_r: TableColumn,
}

impl<F:FieldExt, B:ByteOp> Chip<F> for ByteOpChip<F, B> {
    type Config = ByteOpChipConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: FieldExt, B:ByteOp> ByteOpChip<F, B> {
    fn new(config: ByteOpChipConfig) -> Self {
        ByteOpChip { config, _marker_f: PhantomData, _marker_b: PhantomData }
    }

    fn configure(cs: &mut ConstraintSystem<F>, tbl_col:TableColumn) -> ByteOpChipConfig {
        let l_col = cs.advice_column();
        let r_col = cs.advice_column();
        let o_col = cs.advice_column();
        let tbl_l = cs.lookup_table_column();
        let tbl_r = cs.lookup_table_column();
        let tbl_o = cs.lookup_table_column();

        cs.lookup(|meta| {
          let l_cur = meta.query_advice(l_col, Rotation::cur());
          let r_cur = meta.query_advice(r_col, Rotation::cur());
          let o_cur = meta.query_advice(o_col, Rotation::cur());
          vec![(l_cur, tbl_l), (r_cur, tbl_r), (o_cur, tbl_o)]
        });

        ByteOpChipConfig {
            l_col,
            r_col,
            o_col,
            tbl_l,
            tbl_r,
            tbl_o,
        }
    }

    // `2^BYTE_BITS * 2^BYTE_BITS = 2^16` rows of the constraint system.
    fn alloc_table(&self, layouter: &mut impl Layouter<F>, basis:u32, idx:usize) -> Result<(), Error> {
        layouter.assign_table(
            || "u16-op-table",
            |mut table| {
                for l in 0..1 << BYTE_BITS {
                    for r in 0..1 << BYTE_BITS {
                        let repr = FpRepr::<B>::get_op_entry(BigUint::from(l),
                                BigUint::from(r),
                                basis);
                        println!("l: {}, r: {} v:{:?}", l, r, repr.proj(idx));
                        println!("value: {}", l * (1<<BYTE_BITS) + r);
                        table.assign_cell(
                            || "table_idx",
                            self.config.tbl_o,
                            l * (1<< BYTE_BITS) + r,
                            || Ok(F::from_u64(repr.proj(idx).into()))
                        )?;
                        table.assign_cell(
                            || "table_idx",
                            self.config.tbl_l,
                            l * (1<< BYTE_BITS) + r,
                            || Ok(F::from_u64(l as u64))
                        )?;
                        table.assign_cell(
                            || "table_idx",
                            self.config.tbl_r,
                            l * (1<< BYTE_BITS) + r,
                            || Ok(F::from_u64(r as u64))
                        )?;
                    }
                }
                println!("cb");
                Ok(())
            }
        )
    }

    // Allocates `a`, `b`, and `c` and enables `s_pub` in row #0, i.e. the first available row where
    // the `l_col`, `r_col`, and `o_col` cells have not been alloacted.
    fn alloc_private_and_public_inputs(
        &self,
        layouter: &mut impl Layouter<F>,
        a: Option<F>,
        b: Option<F>,
        c: Option<F>,
    ) -> Result<(), Error> {
        let va = a.unwrap();
        let vb = b.unwrap();
        layouter.assign_region(
            || "private and public inputs",
            |mut region| {
                let row_offset = 0;
                //self.config.s_pub.enable(&mut region, row_offset)?;
                region.assign_advice(
                    || "private input `a`",
                    self.config.l_col,
                    row_offset,
                    || a.ok_or(Error::SynthesisError),
                )?;
                region.assign_advice(
                    || "private input `b`",
                    self.config.r_col,
                    row_offset,
                    || b.ok_or(Error::SynthesisError),
                )?;
                region.assign_advice(
                    || "private input `b`",
                    self.config.o_col,
                    row_offset,
                    || c.ok_or(Error::SynthesisError),
                )?;
                Ok(())
            },
        )
    }
}

#[derive(Clone, Default)]
struct ByteOpCircuit {
    // Private inputs.
    a: Option<Fp>,
    b: Option<Fp>,
    // Public input (from prover).
    c: Option<Fp>,
}

struct PlusOp {
    m: PhantomData<()>
}

impl ByteOp for PlusOp {
    fn bop (x:BigUint, y:BigUint) -> BigUint {
        x + y
    }
}

impl Circuit<Fp> for ByteOpCircuit {
    type Config = ByteOpChipConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
      Self::default()
    }

    fn configure(cs: &mut ConstraintSystem<Fp>) -> Self::Config {
        let tbl_col = cs.lookup_table_column();
        ByteOpChip::<Fp, PlusOp>::configure(cs, tbl_col)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<Fp>) -> Result<(), Error> {
        println!("Start synthesize ...");
        let op_chip = ByteOpChip::<Fp, PlusOp>::new(config);
        println!("CreateOpChip ... Done");
        op_chip.alloc_table(&mut layouter, 0, 0)?;
        println!("AllocTable ... Done");
        op_chip.alloc_private_and_public_inputs(&mut layouter, self.a, self.b, self.c)?;
        println!("AllocPrivate ... Done");
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

    let circuit = ByteOpCircuit {
        a: Some(Fp::from(255)),
        b: Some(Fp::from(255)),
        c: Some(Fp::from(254)),
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

