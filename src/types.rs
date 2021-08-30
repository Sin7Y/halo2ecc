use halo2::{
    arithmetic::FieldExt,
    plonk::{Advice, Column, ConstraintSystem},
    circuit::{Cell}
};

use std::marker::PhantomData;

#[derive(Clone)]
pub struct FieldNum<F:FieldExt> {
    cells: [Cell; 3],
    value: [F;3],
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

/*
impl<F: FieldExt> FieldNumAdvice<F> {
  fn query_advices(&self, meta: &mut ConstraintSystem<F>, r:Rotation)
  -> FieldNumAdvice<F> {
    let r0 = meta.query_advice(self.advices[0], r);
    let r1 = meta.query_advice(self.advices[1], r);
    let r2 = meta.query_advice(self.advices[2], r);
    FieldNumAdvice {
        advices:[r0,r1,r2],
        _marker: PhantomData,
    }
  }
}
*/
