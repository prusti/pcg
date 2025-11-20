use std::marker::PhantomData;

pub(crate) trait DebugRepr<Ctxt = ()> {
    type Repr: serde::Serialize;

    fn debug_repr(&self, ctxt: Ctxt) -> Self::Repr;
}

#[cfg(feature = "type-export")]
pub(crate) trait TypescriptBrand {
    fn brand() -> &'static str;
}

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub struct StringOf<T>(String, PhantomData<T>);

#[cfg(feature = "type-export")]
impl<T: TypescriptBrand> specta::Type for StringOf<T> {
    fn inline(
        type_map: &mut specta::TypeCollection,
        generics: specta::Generics,
    ) -> specta::DataType {
        use std::borrow::Cow;

        use specta::datatype::GenericType;

        specta::datatype::DataType::Generic(GenericType::from(Cow::Owned(format!(
            "StringOf<{}>",
            T::brand()
        ))))
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
    pub(crate) fn new_display(value: T) -> Self {
        Self(value.to_string(), PhantomData)
    }
}

impl<T: std::fmt::Debug> StringOf<T> {
    pub(crate) fn new_debug(value: T) -> Self {
        Self(format!("{value:?}"), PhantomData)
    }
}
