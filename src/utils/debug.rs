use std::marker::PhantomData;

use serde_derive::Serialize;

pub(crate) trait DebugRepr<Ctxt = ()> {
    type Repr: serde::Serialize;

    fn debug_repr(&self, ctxt: Ctxt) -> Self::Repr;
}

#[derive(Serialize)]
pub(crate) struct StringOf<T>(pub String, PhantomData<T>);

impl<T: std::fmt::Display> StringOf<T> {
    pub fn new(value: T) -> Self {
        Self(value.to_string(), PhantomData)
    }
}
