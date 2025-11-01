use serde::Serialize;

pub(crate) trait DebugRepr<Ctxt = ()> {
    type Repr: Serialize;

    fn debug_repr(&self, ctxt: Ctxt) -> Self::Repr;
}
