use std::marker::PhantomData;

pub(crate) trait DebugRepr<Ctxt = ()> {
    type Repr: serde::Serialize;

    fn debug_repr(&self, ctxt: Ctxt) -> Self::Repr;
}

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub struct StringOf<T> {
    value: String,
    _marker: PhantomData<T>,
}

#[cfg(feature = "type-export")]
impl<T: 'static> ts_rs::TS for StringOf<T> {
    type WithoutGenerics = StringOf<ts_rs::Dummy>;
    type OptionInnerType = Self;

    fn name(_: &ts_rs::Config) -> String {
        "string".to_owned()
    }

    fn inline(_: &ts_rs::Config) -> String {
        "string".to_owned()
    }
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
