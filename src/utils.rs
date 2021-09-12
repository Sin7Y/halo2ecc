use std::convert::TryInto;

use num_bigint::BigUint;

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

pub fn decompose_eight_bits<F: PrimeFieldBits>(v: F, num_chunks: usize) -> Vec<u64> {
    let bits: Vec<bool> = v.to_le_bits().into_iter().take(num_chunks * 8).collect();
    bits.chunks_exact(8)
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

pub fn proj<F: FieldExt>(mut bytes: Vec<u8>, i: usize) -> F {
    let chunck_size = [10, 10, 12];
    bytes.resize(32 + chunck_size[2], 0u8);

    if i >= chunck_size.len() {
        return F::from(0);
    } else {
        let start = i * 10;
        let end = start + chunck_size[i];
        return F::from_bytes(&bytes[start..end].try_into().unwrap()).unwrap();
    }
}

pub fn proj_f<Fp: FieldExt, F: FieldExt>(x: Fp, i: usize) -> F {
    return proj(Vec::from(x.to_bytes()), i);
}

pub fn proj_big_uint<F: FieldExt>(x: &BigUint, i: usize) -> F {
    return proj(Vec::from(x.to_bytes_le()), i);
}

pub fn fp_modulus_on_fr<Fp: FieldExt, F: FieldExt>() -> [F; 3] {
    let f_max = Fp::zero() - Fp::one();
    let modulus = BigUint::from_bytes_le(&f_max.to_bytes()) + 1u64;
    let mut ret = [F::zero(); 3];
    for i in 0..3 {
        ret[i] = proj_big_uint(&modulus, i);
    }
    return ret;
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
    )
    .unwrap();

    return a;
}
