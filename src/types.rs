use halo2::{
    arithmetic::FieldExt,
    plonk::{Advice, Column, ConstraintSystem},
    circuit::{Cell}
};

use std::marker::PhantomData;

#[derive(Clone)]
pub struct FieldNum<F:FieldExt> {
    cells: Cell,
    value: F,
}

#[derive(Clone)]
pub struct FieldNumAdvice<F: FieldExt> {
    advices: [Column<Advice>; 3],
    _marker: PhantomData<F>,
}

#[derive(Clone)]
pub struct Number<F: FieldExt> {
    cell: Cell,
    value: Option<F>,
}
