use crate::rustc_interface::{
    index::IndexVec,
    middle::ty::{self, TypeSuperVisitable, TypeVisitable, TypeVisitor},
};

use super::region_projection::{Generalized, LifetimeProjectionIdx, PcgRegion};

struct LifetimeExtractor<'tcx> {
    lifetimes: Vec<ty::Region<'tcx>>,
}

impl<'tcx> TypeVisitor<ty::TyCtxt<'tcx>> for LifetimeExtractor<'tcx> {
    fn visit_ty(&mut self, ty: ty::Ty<'tcx>) {
        match ty.kind() {
            ty::TyKind::Dynamic(_, region, ..) => {
                // TODO: predicates?
                self.visit_region(*region);
            }
            //  TODO: Justify why function pointers are ignored
            ty::TyKind::FnPtr(_, _) => {}
            ty::TyKind::Closure(_, args) => {
                let closure_args = args.as_closure();
                let upvar_tys = closure_args.upvar_tys();
                for ty in upvar_tys {
                    self.visit_ty(ty);
                }
            }
            _ => {
                ty.super_visit_with(self);
            }
        }
    }
    fn visit_region(&mut self, rr: ty::Region<'tcx>) {
        if !self.lifetimes.contains(&rr) {
            self.lifetimes.push(rr);
        }
    }
}

/// Returns all of the (possibly nested) regions in `ty` that could be part of
/// its region projection. In particular, the intention of this function is to
/// *only* return regions that correspond to data borrowed in a type. In
/// particular, for closures / functions, we do not include regions in the input
/// or argument types.
/// If this type is a reference type, e.g. `&'a mut T`, then this will return
/// `'a` and the regions within `T`.
///
/// The resulting list does not contain duplicates, e.g. T<'a, 'a> will return
/// `['a]`. Note that the order of the returned regions is arbitrary, but
/// consistent between calls to types with the same "shape". E.g T<'a, 'b> and
/// T<'c, 'd> will return the same list of regions will return `['a, 'b]` and
/// `['c, 'd]` respectively. This enables substitution of regions to handle
/// moves in the PCG e.g for the statement `let x: T<'a, 'b> = move c: T<'c,
/// 'd>`.
pub(crate) fn extract_regions(ty: ty::Ty<'_>) -> IndexVec<LifetimeProjectionIdx, PcgRegion<'_>> {
    let mut visitor = LifetimeExtractor { lifetimes: vec![] };
    ty.visit_with(&mut visitor);
    visitor.lifetimes.iter().map(|r| (*r).into()).collect()
}

/// A generalized lifetime: either a region or `RegionsIn(τ)` for an opaque
/// type (type parameter or non-normalizable alias).
///
/// See the [_generalized lifetime_ definition](https://prusti.github.io/pcg-docs/function-shapes.html#lifetime-projections).
#[allow(dead_code)]
#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub(crate) enum GeneralizedLifetime<'tcx> {
    Region(PcgRegion<'tcx>),
    RegionsIn(ty::Ty<'tcx>),
}

#[allow(dead_code)]
struct GeneralizedLifetimeExtractor<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    lifetimes: Vec<GeneralizedLifetime<'tcx>>,
}

#[allow(dead_code)]
impl<'tcx> GeneralizedLifetimeExtractor<'tcx> {
    fn push_if_absent(&mut self, gl: GeneralizedLifetime<'tcx>) {
        if !self.lifetimes.contains(&gl) {
            self.lifetimes.push(gl);
        }
    }
}

impl<'tcx> TypeVisitor<ty::TyCtxt<'tcx>> for GeneralizedLifetimeExtractor<'tcx> {
    fn visit_ty(&mut self, ty: ty::Ty<'tcx>) {
        match ty.kind() {
            ty::TyKind::Param(_) => {
                self.push_if_absent(GeneralizedLifetime::RegionsIn(ty));
            }
            ty::TyKind::Alias(..) => {
                let typing_env = ty::TypingEnv::fully_monomorphized();
                if self
                    .tcx
                    .try_normalize_erasing_regions(typing_env, ty)
                    .is_err()
                {
                    self.push_if_absent(GeneralizedLifetime::RegionsIn(ty));
                } else {
                    ty.super_visit_with(self);
                }
            }
            ty::TyKind::Dynamic(_, region, ..) => {
                self.visit_region(*region);
            }
            ty::TyKind::FnPtr(_, _) => {}
            ty::TyKind::Closure(_, args) => {
                let closure_args = args.as_closure();
                for ty in closure_args.upvar_tys() {
                    self.visit_ty(ty);
                }
            }
            _ => {
                ty.super_visit_with(self);
            }
        }
    }
    fn visit_region(&mut self, rr: ty::Region<'tcx>) {
        self.push_if_absent(GeneralizedLifetime::Region(rr.into()));
    }
}

/// Returns the generalized lifetime list for `ty`: all regions and
/// `RegionsIn(τ)` for opaque types (type parameters, non-normalizable
/// aliases), in the order they appear, with duplicates removed.
///
/// See the [`glfts(τ)` definition](https://prusti.github.io/pcg-docs/function-shapes.html#lifetime-projections).
#[allow(dead_code)]
pub(crate) fn extract_generalized_lifetimes<'tcx>(
    ty: ty::Ty<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
) -> IndexVec<LifetimeProjectionIdx<Generalized>, GeneralizedLifetime<'tcx>> {
    let mut visitor = GeneralizedLifetimeExtractor {
        tcx,
        lifetimes: vec![],
    };
    ty.visit_with(&mut visitor);
    visitor.lifetimes.into_iter().collect()
}
