use halo2::{
    arithmetic::FieldExt,
    plonk::{Advice, Column},
    circuit::{Cell}
};

use std::marker::PhantomData;

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

#[derive(Clone, Debug, Copy)]
pub struct Fs<F:FieldExt> {
    pub values: [Number<F>; 3],
}
