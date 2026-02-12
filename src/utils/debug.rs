use std::marker::PhantomData;

pub(crate) trait DebugRepr<Ctxt = ()> {
    type Repr: serde::Serialize;

    fn debug_repr(&self, ctxt: Ctxt) -> Self::Repr;
}

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
#[cfg_attr(feature = "type-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "type-export", ts(type="string",concrete(T=String)))]
pub struct StringOf<T> {
    value: String,
    _marker: PhantomData<T>,
}

impl<T> serde::Serialize for StringOf<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.value.serialize(serializer)
    }
}

impl<T: std::fmt::Display> StringOf<T> {
    pub(crate) fn new_display(value: T) -> Self {
        Self {
            value: value.to_string(),
            _marker: PhantomData,
        }
    }
}

impl<T: std::fmt::Debug> StringOf<T> {
    pub(crate) fn new_debug(value: T) -> Self {
        Self {
            value: format!("{value:?}"),
            _marker: PhantomData,
        }
    }
}
