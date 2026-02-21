use crate::error::PcgUnsupportedError;
use crate::utils::{HasCompilerCtxt, PcgPlace, Place, place::PlaceExpansion};
use crate::rustc_interface::middle::mir::{Local, ProjectionElem};
pub trait PlaceLike<'tcx, Ctxt: Copy>: PcgPlace<'tcx, Ctxt> + From<Local> {
    fn local(self) -> Local;
    fn is_owned(self, ctxt: Ctxt) -> bool;
    fn projects_indirection_from(self, other: Self, ctxt: Ctxt) -> bool;
    fn expansion_places(
        self,
        expansion: &PlaceExpansion<'tcx>,
        ctxt: Ctxt,
    ) -> std::result::Result<Vec<Self>, PcgUnsupportedError<'tcx>>;
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> PlaceLike<'tcx, Ctxt> for Place<'tcx> {
    fn local(self) -> Local {
        self.0.local
    }
    fn is_owned(self, ctxt: Ctxt) -> bool {
        !self
            .iter_projections(ctxt.ctxt())
            .into_iter()
            .any(|(place, elem)| elem == ProjectionElem::Deref && !place.ty(ctxt).ty.is_box())
    }

    fn projects_indirection_from(self, other: Self, ctxt: Ctxt) -> bool {
        let Some(mut projections_after) = self.iter_projections_after(other, ctxt) else {
            return false;
        };
        projections_after.any(|(p, elem)| matches!(elem, ProjectionElem::Deref) && p.is_ref(ctxt))
    }

    fn expansion_places(
        self,
        expansion: &PlaceExpansion<'tcx>,
        ctxt: Ctxt,
    ) -> std::result::Result<Vec<Self>, PcgUnsupportedError<'tcx>> {
        let mut places = Vec::new();
        for (elem, _) in expansion.elems_data() {
            let place = self.project_deeper(elem, ctxt)?;
            places.push(place);
        }
        Ok(places)
    }
}
