use crate::{
    Sealed,
    borrow_pcg::unblock_graph::BorrowPcgUnblockAction,
    error::{IllegalProjection, PcgError, PcgUnsupportedError},
    rustc_interface::middle::{
        mir::{PlaceElem, ProjectionElem},
        ty,
    },
    utils::{HasCompilerCtxt, Place, display::DisplayWithCtxt},
};
pub trait PlaceProjectable<'tcx, Ctxt>: Sized {
    /// Projects the place deeper by one element.
    ///
    /// __IMPORTANT__: This method also attempts to "normalize" the type of the resulting
    /// place by inheriting from the type of the current place when possible. For example,
    /// in the following code:
    /// ```ignore
    /// struct F<'a>(&'a mut i32);
    /// let x: F<'x> = F(&mut 1);
    /// let y: 'y mut i32 = x.0
    /// ```
    /// we want the type of `x.0` to be 'x mut i32 and NOT 'y mut i32. However, in the
    /// MIR the `ProjectionElem::Field` for `.0` may have the type `'y mut i32`.
    ///
    /// To correct this, when projecting, we detect when the LHS is an ADT, and
    /// extract from the ADT type the expected type of the projection and
    /// replace the type.
    ///
    /// Returns an error if the projection would be illegal
    fn project_deeper(
        &self,
        elem: PlaceElem<'tcx>,
        ctxt: Ctxt,
    ) -> std::result::Result<Self, PcgError<'tcx>>;

    fn project_deref(&self, ctxt: Ctxt) -> std::result::Result<Self, PcgError<'tcx>> {
        self.project_deeper(PlaceElem::Deref, ctxt)
    }

    fn iter_projections(&self, ctxt: Ctxt) -> Vec<(Self, PlaceElem<'tcx>)>;
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> PlaceProjectable<'tcx, Ctxt> for Place<'tcx> {
    fn project_deeper(&self, elem: PlaceElem<'tcx>, ctxt: Ctxt) -> Result<Self, PcgError<'tcx>> {
        self.project_elem(elem, ctxt).map_err(|err|PcgError::internal(format!("{:?}", err)))
    }
    fn iter_projections(&self, _ctxt: Ctxt) -> Vec<(Self, PlaceElem<'tcx>)> {
        self.0
            .iter_projections()
            .map(|(place, elem)| (place.into(), elem))
            .collect()
    }
}

impl<'tcx> Place<'tcx> {
    pub(crate) fn project_elem<'a, Ctxt: HasCompilerCtxt<'a, 'tcx>>(
        &self,
        elem: PlaceElem<'tcx>,
        ctxt: Ctxt,
    ) -> Result<Self, IllegalProjection<'tcx>>
    where
        'tcx: 'a,
    {
        let base_ty = self.ty(ctxt);
        IllegalProjection::check(base_ty.ty, elem)?;
        let corrected_elem = if let ProjectionElem::Field(field_idx, proj_ty) = elem {
            let expected_ty = match base_ty.ty.kind() {
                ty::TyKind::Adt(def, substs) => {
                    let variant = match base_ty.variant_index {
                        Some(v) => def.variant(v),
                        None => def.non_enum_variant(),
                    };
                    variant.fields[field_idx].ty(ctxt.tcx(), substs)
                }
                ty::TyKind::Tuple(tys) => tys[field_idx.as_usize()],
                _ => proj_ty,
            };
            ProjectionElem::Field(field_idx, expected_ty)
        } else {
            elem
        };
        Ok(self.0.project_deeper(&[corrected_elem], ctxt.tcx()).into())
    }
}
