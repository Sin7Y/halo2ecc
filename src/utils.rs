use std::convert::TryInto;

use halo2::{arithmetic::FieldExt, plonk::Expression, poly::Rotation};

use ff::PrimeFieldBits;

pub fn pow2<F: FieldExt>(y: u64) -> F {
    let mut times = y as u64;
    let mut curr = F::from_u64(2u64);
    let mut acc = F::from_u64(1);
    while times > 0 {
        if times & 1 == 1 {
            acc = acc * curr;
        }
        curr = curr * curr;
        times >>= 1;
    }
    return acc;
}

pub fn decompose_four_bits<F: PrimeFieldBits>(v: F, num_bits: usize) -> Vec<u8> {
    let bits: Vec<bool> = v.to_le_bits().into_iter().take(num_bits).collect();
    bits.chunks_exact(num_bits)
        .map(|chunk| chunk.iter().rev().fold(0, |acc, b| (acc << 1) + (*b as u8)))
        .collect()
}

pub fn decompose_tweleve_bits<F: PrimeFieldBits>(v: F, num_chunks: usize) -> Vec<u64> {
    let bits: Vec<bool> = v.to_le_bits().into_iter().take(num_chunks * 12).collect();
    bits.chunks_exact(12)
        .map(|chunk| {
            chunk
                .iter()
                .rev()
                .fold(0, |acc, b| (acc << 1) + (*b as u64))
        })
        .collect()
}

pub fn to_expr<F: FieldExt>(x: u64) -> Expression<F> {
    Expression::Constant(F::from_u64(x))
}

pub fn projF<Fp: FieldExt, F: FieldExt>(x: Fp, i: usize) -> F {
    if i > 2 {
        return F::from(0);
    } else if i == 2 {
        return F::from_bytes(
            &[&x.to_bytes()[20..32], &[0u8; 20][..]]
                .concat()
                .try_into()
                .unwrap(),
        )
        .unwrap();
    } else if i == 1 {
        return F::from_bytes(
            &[&x.to_bytes()[10..20], &[0u8; 22][..]]
                .concat()
                .try_into()
                .unwrap(),
        )
        .unwrap();
    } else {
        return F::from_bytes(
            &[&x.to_bytes()[0..10], &[0u8; 22][..]]
                .concat()
                .try_into()
                .unwrap(),
        )
        .unwrap();
    }
}

pub fn get_shift_lookup<F: FieldExt>(x: F, shift: u64) -> F {
    return x * pow2::<F>(shift * 8 + 240);
}

pub fn N_div_256<F: FieldExt>(x: F) -> F {
    let a = F::from_bytes(
        &[&x.to_bytes()[1..32], &[0u8; 1][..]]
            .concat()
            .try_into()
            .unwrap(),
    ).unwrap();

    return a;
}
