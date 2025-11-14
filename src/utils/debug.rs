use std::marker::PhantomData;

pub(crate) trait DebugRepr<Ctxt = ()> {
    type Repr: serde::Serialize;

    fn debug_repr(&self, ctxt: Ctxt) -> Self::Repr;
}

#[derive(Hash, PartialEq, Eq)]
pub struct StringOf<T>(pub String, PhantomData<T>);

#[cfg(feature = "type-export")]
impl<T> specta::Type for StringOf<T> {
    fn inline(
        type_map: &mut specta::TypeCollection,
        _generics: specta::Generics,
    ) -> specta::DataType {
        <String as specta::Type>::inline(type_map, specta::Generics::Provided(&[]))
    }
}

impl<T> serde::Serialize for StringOf<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.0.serialize(serializer)
    }
}

impl<T: std::fmt::Display> StringOf<T> {
    pub(crate) fn new(value: T) -> Self {
        Self(value.to_string(), PhantomData)
    }
}

impl<T: std::fmt::Debug> StringOf<T> {
    pub(crate) fn new_debug(value: T) -> Self {
        Self(format!("{value:?}"), PhantomData)
    }
}
