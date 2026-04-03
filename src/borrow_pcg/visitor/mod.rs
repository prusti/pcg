use std::{collections::HashMap, hash::Hash};

use crate::rustc_interface::{
    index::IndexVec,
    middle::ty::{self, TypeSuperVisitable, TypeVisitable, TypeVisitor},
};

use super::region_projection::{Generalized, LifetimeProjectionIdx, PcgRegion, Region};

/// Trait abstracting over region extraction strategies.
///
/// Implementors define which "lifetime-like" values are extracted from a type
/// and which [`LifetimeProjectionIdx`] kind they correspond to. The two
/// implementations are:
///
/// - [`PcgRegion`]: extracts concrete regions (lifetime projections).
/// - [`GeneralizedLifetime`]: extracts regions *and* `RegionsIn(τ)` for opaque
///   types (generalized lifetime projections).
pub trait LifetimeKind<'tcx>: Sized + Copy + PartialEq + Eq + std::fmt::Debug + Hash {
    /// The index kind: [`Region`] for lifetime projections, [`Generalized`]
    /// for generalized lifetime projections.
    type IdxKind: super::region_projection::RegionIdxKind;

    /// Extract all lifetime-like values from `ty`.
    fn extract(
        ty: ty::Ty<'tcx>,
        tcx: ty::TyCtxt<'tcx>,
    ) -> IndexVec<LifetimeProjectionIdx<Self::IdxKind>, Self>;

    /// Whether this lifetime appears in an invariant (mutable) position in `ty`.
    fn is_invariant_in_type(self, ty: ty::Ty<'tcx>, tcx: ty::TyCtxt<'tcx>) -> bool;
}

impl<'tcx> LifetimeKind<'tcx> for PcgRegion<'tcx> {
    type IdxKind = Region;

    fn extract(
        ty: ty::Ty<'tcx>,
        _tcx: ty::TyCtxt<'tcx>,
    ) -> IndexVec<LifetimeProjectionIdx<Region>, Self> {
        extract_regions(ty)
    }

    fn is_invariant_in_type(self, ty: ty::Ty<'tcx>, tcx: ty::TyCtxt<'tcx>) -> bool {
        super::region_projection::region_is_invariant_in_type(tcx, self, ty)
    }
}

impl<'tcx> LifetimeKind<'tcx> for GeneralizedLifetime<'tcx> {
    type IdxKind = Generalized;

    fn extract(
        ty: ty::Ty<'tcx>,
        _tcx: ty::TyCtxt<'tcx>,
    ) -> IndexVec<LifetimeProjectionIdx<Generalized>, Self> {
        extract_generalized_lifetimes(ty)
    }

    fn is_invariant_in_type(self, ty: ty::Ty<'tcx>, tcx: ty::TyCtxt<'tcx>) -> bool {
        match self {
            GeneralizedLifetime::Region(region) => {
                super::region_projection::region_is_invariant_in_type(tcx, region, ty)
            }
            // A type parameter `T` that appears in the type is always
            // considered invariant — any borrows hidden inside could be
            // affected by the function.
            GeneralizedLifetime::RegionsIn(_param_ty) => true,
        }
    }
}

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

/// An opaque type whose internal structure is not visible for lifetime
/// extraction: either a type parameter (`T`, `Self`) or a non-normalizable
/// associated type (`<Self as Deref>::Target`).
#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum OpaqueTy<'tcx> {
    /// A type parameter (e.g., `T`, `Self`).
    Param(ty::ParamTy),
    /// A non-normalizable alias type (e.g., `<Self as Deref>::Target`).
    Alias(ty::AliasTy<'tcx>),
}

impl<'tcx> TryFrom<ty::Ty<'tcx>> for OpaqueTy<'tcx> {
    type Error = ();

    fn try_from(ty: ty::Ty<'tcx>) -> Result<Self, Self::Error> {
        match ty.kind() {
            ty::TyKind::Param(param_ty) => Ok(Self::Param(*param_ty)),
            ty::TyKind::Alias(_, alias_ty) => Ok(Self::Alias(*alias_ty)),
            _ => Err(()),
        }
    }
}

impl<'tcx> OpaqueTy<'tcx> {
    /// Returns the underlying type as a `ty::Ty`.
    pub fn ty(self, tcx: ty::TyCtxt<'tcx>) -> ty::Ty<'tcx> {
        match self {
            Self::Param(param_ty) => ty::Ty::new_param(tcx, param_ty.index, param_ty.name),
            Self::Alias(alias_ty) => alias_ty.to_ty(tcx),
        }
    }

    /// Returns `true` if this is a type parameter.
    pub fn is_param(self) -> bool {
        matches!(self, Self::Param(_))
    }
}

impl std::fmt::Display for OpaqueTy<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Param(param_ty) => write!(f, "{}", param_ty.name),
            Self::Alias(alias_ty) => write!(f, "{alias_ty:?}"),
        }
    }
}

/// A generalized lifetime: either a region or `RegionsIn(τ)` for an opaque
/// type (type parameter or non-normalizable alias).
///
/// See the [_generalized lifetime_ definition](https://prusti.github.io/pcg-docs/function-shapes.html#lifetime-projections).
#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum GeneralizedLifetime<'tcx> {
    Region(PcgRegion<'tcx>),
    RegionsIn(OpaqueTy<'tcx>),
}

struct GeneralizedLifetimeExtractor<'a, 'tcx> {
    lifetimes: Vec<GeneralizedLifetime<'tcx>>,
    /// When provided, trait-bound regions for type parameters are included
    /// as separate `Region(r)` entries after the `RegionsIn(T)` entry.
    trait_bound_regions: Option<&'a HashMap<OpaqueTy<'tcx>, Vec<ty::Region<'tcx>>>>,
}

impl<'tcx> GeneralizedLifetimeExtractor<'_, 'tcx> {
    fn push_if_absent(&mut self, gl: GeneralizedLifetime<'tcx>) {
        if !self.lifetimes.contains(&gl) {
            self.lifetimes.push(gl);
        }
    }

    /// After pushing `RegionsIn(opaque_ty)` for a type parameter or alias,
    /// also push any trait-bound regions as separate `Region(r)` entries.
    fn push_trait_bound_regions_for(&mut self, opaque_ty: OpaqueTy<'tcx>) {
        if let Some(tbr) = self.trait_bound_regions
            && let Some(regions) = tbr.get(&opaque_ty)
        {
            for &r in regions {
                self.push_if_absent(GeneralizedLifetime::Region(r.into()));
            }
        }
    }
}

impl<'tcx> TypeVisitor<ty::TyCtxt<'tcx>> for GeneralizedLifetimeExtractor<'_, 'tcx> {
    fn visit_ty(&mut self, ty: ty::Ty<'tcx>) {
        match ty.kind() {
            ty::TyKind::Param(param_ty) => {
                let opaque = OpaqueTy::Param(*param_ty);
                self.push_if_absent(GeneralizedLifetime::RegionsIn(opaque));
                self.push_trait_bound_regions_for(opaque);
            }
            ty::TyKind::Alias(_, alias_ty) => {
                let opaque = OpaqueTy::Alias(*alias_ty);
                self.push_if_absent(GeneralizedLifetime::RegionsIn(opaque));
                self.push_trait_bound_regions_for(opaque);
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
pub(crate) fn extract_generalized_lifetimes(
    ty: ty::Ty<'_>,
) -> IndexVec<LifetimeProjectionIdx<Generalized>, GeneralizedLifetime<'_>> {
    let mut visitor = GeneralizedLifetimeExtractor {
        lifetimes: vec![],
        trait_bound_regions: None,
    };
    ty.visit_with(&mut visitor);
    visitor.lifetimes.into_iter().collect()
}

/// Like [`extract_generalized_lifetimes`], but also includes regions from
/// trait bounds of type parameters. For a type parameter `T` with bound
/// `T: Foo<'a, 'b>`, the resulting list will contain `RegionsIn(T)` followed
/// by `Region('a)` and `Region('b)`.
pub(crate) fn extract_generalized_lifetimes_with_bounds<'tcx>(
    ty: ty::Ty<'tcx>,
    trait_bound_regions: &HashMap<OpaqueTy<'tcx>, Vec<ty::Region<'tcx>>>,
) -> IndexVec<LifetimeProjectionIdx<Generalized>, GeneralizedLifetime<'tcx>> {
    let mut visitor = GeneralizedLifetimeExtractor {
        lifetimes: vec![],
        trait_bound_regions: Some(trait_bound_regions),
    };
    ty.visit_with(&mut visitor);
    visitor.lifetimes.into_iter().collect()
}
