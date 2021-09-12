use halo2::{
    arithmetic::FieldExt,
    circuit::Region,
    plonk::{ConstraintSystem, Expression, Error},
};
use num_bigint::BigUint;
use std::convert::TryInto;
use std::marker::PhantomData;

use crate::types::{Fs, FsAdvice, Number};

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
        return F::from_bytes(
            &[&bytes[start..end], &[0u8; 32][..(32 - chunck_size[i])]]
                .concat()
                .try_into()
                .unwrap(),
        )
        .unwrap();
    }
}

pub fn fp_on_fr_to_big_uint<F: FieldExt>(x: [F; 3]) -> BigUint {
    let bytes = [
        &x[0].to_bytes()[0..10],
        &x[1].to_bytes()[0..10],
        &x[2].to_bytes()[0..12],
    ]
    .concat();

    return BigUint::from_bytes_le(&bytes);
}

pub fn proj_f<Fp: FieldExt, F: FieldExt>(x: Fp, i: usize) -> F {
    return proj(Vec::from(x.to_bytes()), i);
}

pub fn proj_big_uint<F: FieldExt>(x: &BigUint, i: usize) -> F {
    return proj(Vec::from(x.to_bytes_le()), i);
}

pub fn big_unit_from_f<F: FieldExt>(a: F) -> BigUint {
    return BigUint::from_bytes_le(&a.to_bytes());
}

pub fn fp_modulus_on_big_uint<Fp: FieldExt>() -> BigUint {
    let f_max = Fp::zero() - Fp::one();
    let modulus = big_unit_from_f(f_max) + 1u64;
    return modulus;
}

pub fn f_from_big_unit<F: FieldExt>(x: &BigUint) -> F {
    let mut bytes = x.to_bytes_le();
    bytes.resize(32, 0u8);
    return F::from_bytes(&bytes.try_into().unwrap()).unwrap();
}

pub fn fp_on_fr_from_big_unit<F: FieldExt>(x: BigUint) -> [F; 3] {
    let mut ret = [F::zero(); 3];
    for i in 0..3 {
        ret[i] = proj_big_uint(&x, i);
    }
    return ret;
}

pub fn fp_modulus_on_fr<Fp: FieldExt, F: FieldExt>() -> [F; 3] {
    let modulus = fp_modulus_on_big_uint::<Fp>();
    return fp_on_fr_from_big_unit(modulus);
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

pub fn assign_fs<F: FieldExt>(
    region: &mut Region<F>,
    a: FsAdvice<F>,
    o: &Fs<F>,
    row_offset: usize,
    hint: &str,
) -> Result<Fs<F>, Error> {
    let mut numbers = vec![];

    for i in 0..3 {
        let value = o.values[i].value;
        let cell = region
            .assign_advice(
                || format!("{}_{}", hint, i),
                a.advices[i],
                row_offset + i,
                || Ok(value.unwrap()),
            )
            .unwrap();

        numbers.push(Number::<F> { cell, value });
        region.constrain_equal(cell, o.values[i].cell)?;
    }

    Ok(Fs::<F> {
        values: numbers.try_into().unwrap(),
    })
}

pub fn assign_fp<F: FieldExt>(
    region: &mut Region<F>,
    a: FsAdvice<F>,
    o: [F; 3],
    row_offset: usize,
    hint: &str,
) -> Fs<F> {
    let mut numbers = vec![];

    for i in 0..3 {
        let value = Some(o[i]);
        let cell = region
            .assign_advice(
                || format!("{}_{}", hint, i),
                a.advices[i],
                row_offset,
                || Ok(value.unwrap()),
            )
            .unwrap();

        numbers.push(Number::<F> { cell, value });
    }

    Fs::<F> {
        values: numbers.try_into().unwrap(),
    }
}

/// a * b + c === ret[0] + (ret[1] << 160)  + (ret[2] << 240) + (ret[3] <<320)
pub fn fp_on_fr_mul_plus<F: FieldExt>(a: [F; 3], b: [F; 3], c: [F; 3]) -> [F; 4] {
    let shift_80 = pow2::<F>(80);

    return [
        a[2].clone() * b[2].clone(),
        a[2].clone() * b[1].clone() + a[1].clone() * b[2],
        a[2].clone() * b[0].clone()
            + a[1].clone() * b[1].clone()
            + a[0].clone() * b[2].clone()
            + c[2],
        (a[0].clone() * b[1].clone() + a[1].clone() * b[0].clone()) * shift_80
            + a[0].clone() * b[0].clone()
            + c[0]
            + c[1] * shift_80,
    ];
}

pub fn advice_fs_column<F: FieldExt>(meta: &mut ConstraintSystem<F>) -> FsAdvice<F> {
    return FsAdvice::<F> {
        advices: [
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
        ],
        _marker: PhantomData,
    };
}
