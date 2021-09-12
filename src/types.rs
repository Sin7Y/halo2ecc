use halo2::{
    arithmetic::FieldExt,
    plonk::{Advice, Column, ConstraintSystem},
    circuit::{Cell}
};

use std::marker::PhantomData;
use ff::PrimeFieldBits;

#[derive(Clone, Debug, Copy)]
pub struct FsAdvice<F: FieldExt> {
    pub advices: [Column<Advice>; 3],
    pub _marker: PhantomData<F>,
}

#[derive(Clone, Debug, Copy)]
pub struct Number<F: FieldExt> {
    pub cell: Cell,
    pub value: Option<F>,
}

#[derive(Clone, Debug)]
pub struct Fs<F:FieldExt> {
    pub values: [Number<F>; 3],
}
