//! The region variables of a borrow-checked body that stand for the lifetime
//! parameters of its function.
//!
//! The where clauses of a function name its lifetime parameters, the types of
//! its borrow-checked body only region variables. rustc's borrow checker gives
//! each lifetime parameter a universal region variable, numbered `'static`
//! first, then the lifetime parameters in the order of the identity arguments
//! of the typeck root: the function, or for a closure the function that defines
//! it (`UniversalRegions` in `rustc_borrowck`, which is not public). This module
//! is the one place that relies on this numbering; C4 (`spec::check_body_spec`)
//! checks it against the body's region inference.

#[rustversion::since(2026-07-21)]
use crate::rustc_interface::middle::ty::RegionExt;
use crate::rustc_interface::{
    hir::def_id::DefId,
    middle::ty::{self, RegionVid},
};

/// The universal region variables of the lifetime parameters of a body.
#[derive(Clone, Copy)]
pub(crate) struct BodyRegions<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    /// The typeck root of the body.
    root: DefId,
}

impl<'tcx> BodyRegions<'tcx> {
    /// The universal regions of the body of `def_id`.
    pub(crate) fn new(tcx: ty::TyCtxt<'tcx>, def_id: DefId) -> Self {
        Self {
            tcx,
            root: tcx.typeck_root_def_id(def_id),
        }
    }

    /// The lifetime parameters, in the order of their region variables after
    /// the one of `'static`.
    fn params(self) -> impl Iterator<Item = ty::EarlyParamRegion> {
        ty::GenericArgs::identity_for_item(self.tcx, self.root)
            .regions()
            .map(|region| match region.kind() {
                ty::RegionKind::ReEarlyParam(param) => param,
                _ => unreachable!("{region:?} is not a lifetime parameter"),
            })
    }

    /// The region variable of the lifetime parameter `param`.
    pub(crate) fn universal_vid(self, param: ty::EarlyParamRegion) -> RegionVid {
        let position = self
            .params()
            .position(|p| p == param)
            .unwrap_or_else(|| panic!("{param:?} is not a lifetime parameter of {:?}", self.root));
        RegionVid::from_usize(1 + position)
    }

    /// The lifetime parameter whose region variable is `vid`, if any.
    pub(crate) fn param_of(self, vid: RegionVid) -> Option<ty::EarlyParamRegion> {
        vid.as_usize()
            .checked_sub(1)
            .and_then(|position| self.params().nth(position))
    }

    /// `value` with its lifetime parameters replaced by their region
    /// variables.
    pub(crate) fn params_to_vids<T: ty::TypeFoldable<ty::TyCtxt<'tcx>>>(self, value: T) -> T {
        ty::fold_regions(self.tcx, value, |region, _| match region.kind() {
            ty::RegionKind::ReEarlyParam(param) => {
                ty::Region::new_var(self.tcx, self.universal_vid(param))
            }
            _ => region,
        })
    }

    /// `value` with the region variables of lifetime parameters replaced by
    /// the parameters.
    pub(crate) fn vids_to_params<T: ty::TypeFoldable<ty::TyCtxt<'tcx>>>(self, value: T) -> T {
        ty::fold_regions(self.tcx, value, |region, _| match region.kind() {
            ty::RegionKind::ReVar(vid) => self
                .param_of(vid)
                .map_or(region, |param| ty::Region::new_early_param(self.tcx, param)),
            _ => region,
        })
    }
}
