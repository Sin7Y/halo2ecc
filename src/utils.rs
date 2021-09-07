use halo2::{
    arithmetic::FieldExt,
    plonk::Expression,
    poly::Rotation,
};

use ff::PrimeFieldBits;

pub fn decompose_four_bits<F:PrimeFieldBits> (v: F, num_bits:usize) -> Vec<u8>{
    let bits: Vec<bool> = v.to_le_bits()
        .into_iter()
        .take(num_bits)
        .collect();
    bits.chunks_exact(num_bits)
        .map(|chunk| chunk.iter().rev().fold(0, |acc, b| (acc << 1) + (*b as u8)))
        .collect()
}

pub fn decompose_tweleve_bits<F:PrimeFieldBits> (v: F, num_chunks:usize) -> Vec<u64>{
    let bits: Vec<bool> = v.to_le_bits()
        .into_iter()
        .take(num_chunks * 12)
        .collect();
    bits.chunks_exact(12)
        .map(|chunk| chunk.iter().rev().fold(0, |acc, b| (acc << 1) + (*b as u64)))
        .collect()
}


pub fn to_expr<F:FieldExt>(x:u64) ->Expression<F> {
    Expression::Constant(F::from_u64(x))
}

pub fn get_shift_lookup<F:FieldExt>(x: F, shift: F) -> F {
    F::zero()
}


