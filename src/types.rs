use halo2::{
    arithmetic::FieldExt,
    circuit::{Cell}
};

#[derive(Clone)]
pub struct FieldNum<F:FieldExt> {
    cells: [Cell; 3],
    value: [F;3],
}

#[derive(Clone)]
pub struct Number<F: FieldExt> {
    cell: Cell,
    value: Option<F>,
}



