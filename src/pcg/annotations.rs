use std::marker::PhantomData;

use serde_json::json;

use crate::{
    pcg::PositiveCapability,
    utils::{
        HasBorrowCheckerCtxt, HasCompilerCtxt, Place,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
        json::ToJsonWithCtxt,
    },
};

/// Instructs that the capability to the place should be restored to the
/// given capability, e.g. after a borrow expires, the borrowed place should be
/// restored to exclusive capability.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct RestoreCapability<'tcx, P = Place<'tcx>> {
    place: P,
    capability: PositiveCapability,
    _marker: PhantomData<&'tcx ()>,
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> ToJsonWithCtxt<Ctxt>
    for RestoreCapability<'tcx>
{
    fn to_json(&self, ctxt: Ctxt) -> serde_json::Value {
        json!({
            "place": self.place.to_json(ctxt.ctxt()),
            "capability": format!("{:?}", self.capability),
        })
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for RestoreCapability<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        DisplayOutput::join(
            vec![
                "Restore".into(),
                self.place.display_output(ctxt, mode),
                "to".into(),
                self.capability.display_output(ctxt, mode),
            ],
            &DisplayOutput::SPACE,
        )
    }
}

impl<P: Copy> RestoreCapability<'_, P> {
    pub(crate) fn new(place: P, capability: PositiveCapability) -> Self {
        Self {
            place,
            capability,
            _marker: PhantomData,
        }
    }

    pub fn place(&self) -> P {
        self.place
    }

    pub fn capability(&self) -> PositiveCapability {
        self.capability
    }
}

impl RestoreCapability<'_> {}
