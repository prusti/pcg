// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{
    hash::{Hash, Hasher},
    mem::discriminant,
};

use crate::{
    Sealed,
    borrow_pcg::region_projection::HasTy,
    error::PlaceContainingPtrWithNestedLifetime,
    rustc_interface::{
        VariantIdx,
        ast::Mutability,
        middle::{
            mir::{Local, Place as MirPlace, PlaceElem, PlaceRef, ProjectionElem},
            ty::{self, Ty, TyKind},
        },
    },
    utils::{HasCompilerCtxt, data_structures::HashSet, json::ToJsonWithCtxt},
};
use derive_more::{Deref, DerefMut};

use super::{CompilerCtxt, display::DisplayWithCompilerCtxt};
use crate::borrow_pcg::{
    region_projection::{LifetimeProjection, PcgRegion, RegionIdx},
    visitor::extract_regions,
};

pub mod corrected;
pub(crate) mod display;
pub(crate) mod expansion;
pub mod maybe_old;
pub mod maybe_remote;
pub(crate) mod ordering;
pub(crate) mod pcg_place;
pub(crate) mod place_like;
pub(crate) mod place_projectable;
pub mod remote;
pub use expansion::PlaceExpansion;
pub use ordering::PrefixRelation;
pub use pcg_place::PcgPlace;
pub use place_like::PlaceLike;
pub use place_projectable::PlaceProjectable;
#[derive(Clone, Copy, Deref, DerefMut)]
#[cfg_attr(feature = "type-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "type-export", ts(as = "String"))]
pub struct Place<'tcx>(
    #[deref]
    #[deref_mut]
    PlaceRef<'tcx>,
);

impl Sealed for Place<'_> {}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> HasTy<'tcx, Ctxt> for Place<'tcx> {
    fn rust_ty(&self, ctxt: Ctxt) -> ty::Ty<'tcx> {
        self.0.ty(ctxt.body(), ctxt.tcx()).ty
    }
}

impl<'tcx> From<crate::utils::mir::Local> for Place<'tcx> {
    fn from(local: crate::utils::mir::Local) -> Self {
        (*local).into()
    }
}

impl<'tcx> From<Place<'tcx>> for PlaceRef<'tcx> {
    fn from(place: Place<'tcx>) -> Self {
        *place
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> ToJsonWithCtxt<Ctxt> for Place<'tcx> {
    fn to_json(&self, ctxt: Ctxt) -> serde_json::Value {
        serde_json::Value::String(self.display_string(ctxt))
    }
}

pub trait PcgNodeComponent = Copy + Eq + std::hash::Hash + std::fmt::Debug;

/// A trait for PCG nodes that contain a single place.
pub trait HasPlace<'tcx, P = Place<'tcx>>: Sized {
    fn is_place(&self) -> bool;

    fn place(&self) -> P;

    fn place_mut(&mut self) -> &mut P;
}

impl<'tcx> HasPlace<'tcx> for Place<'tcx> {
    fn place(&self) -> Place<'tcx> {
        *self
    }
    fn place_mut(&mut self) -> &mut Place<'tcx> {
        self
    }

    fn is_place(&self) -> bool {
        true
    }
}

impl<'tcx> Place<'tcx> {

    #[rustversion::since(2025-03-01)]
    pub(crate) fn is_raw_ptr<'a>(&self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> bool
    where
        'tcx: 'a,
    {
        self.ty(ctxt).ty.is_raw_ptr()
    }

    #[rustversion::before(2025-03-01)]
    pub(crate) fn is_raw_ptr<'a>(&self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> bool
    where
        'tcx: 'a,
    {
        self.rust_ty(ctxt).is_unsafe_ptr()
    }

    pub(crate) fn parent_place(self) -> Option<Self> {
        let (prefix, _) = self.last_projection()?;
        Some(Place::new(prefix.local, prefix.projection))
    }
}

impl<'tcx> Place<'tcx> {
    #[must_use]
    pub fn new(local: Local, projection: &'tcx [PlaceElem<'tcx>]) -> Self {
        Self(PlaceRef { local, projection })
    }

    pub(crate) fn base_lifetime_projection<'a>(
        self,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Option<LifetimeProjection<'tcx, Self>>
    where
        'tcx: 'a,
    {
        self.ty_region(ctxt)
            .map(|region| LifetimeProjection::new(self, region, None, ctxt.ctxt()).unwrap())
    }

    #[must_use]
    pub fn projection(&self) -> &'tcx [PlaceElem<'tcx>] {
        self.0.projection
    }

    pub(crate) fn contains_unsafe_deref<'a>(&self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> bool
    where
        'tcx: 'a,
    {
        for (p, proj) in self.iter_projections(ctxt.ctxt()) {
            if p.is_raw_ptr(ctxt) && matches!(proj, PlaceElem::Deref) {
                return true;
            }
        }
        false
    }

    pub(crate) fn check_lifetimes_under_unsafe_ptr<'a>(
        self,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> std::result::Result<(), PlaceContainingPtrWithNestedLifetime<'tcx>>
    where
        'tcx: 'a,
    {
        fn ty_has_lifetimes_under_unsafe_ptr<'a, 'tcx>(
            ty: Ty<'tcx>,
            seen: &mut HashSet<Ty<'tcx>>,
            ctxt: impl HasCompilerCtxt<'a, 'tcx>,
        ) -> std::result::Result<(), Vec<ty::Ty<'tcx>>>
        where
            'tcx: 'a,
        {
            if seen.contains(&ty) {
                return Ok(());
            }
            seen.insert(ty);
            if extract_regions(ty).is_empty() {
                return Ok(());
            }
            #[rustversion::before(2025-03-01)]
            let is_raw_ptr = ty.is_unsafe_ptr();
            #[rustversion::since(2025-03-01)]
            let is_raw_ptr = ty.is_raw_ptr();
            if is_raw_ptr {
                return std::result::Result::Err(vec![ty]);
            }
            let field_tys: Vec<Ty<'tcx>> = match ty.kind() {
                TyKind::Array(ty, _) | TyKind::Slice(ty) | TyKind::Ref(_, ty, _) => vec![*ty],
                TyKind::Adt(def, substs) => {
                    if ty.is_box() {
                        vec![substs.first().unwrap().expect_ty()]
                    } else {
                        def.all_fields()
                            .map(|f| f.ty(ctxt.tcx(), substs))
                            .collect::<Vec<_>>()
                    }
                }
                TyKind::Tuple(slice) => slice.iter().collect::<Vec<_>>(),
                TyKind::Closure(_, substs) => {
                    substs.as_closure().upvar_tys().iter().collect::<Vec<_>>()
                }
                TyKind::Coroutine(_, _) | TyKind::CoroutineClosure(_, _) | TyKind::FnDef(_, _) => {
                    vec![]
                }
                TyKind::Alias(_, _)
                | TyKind::Dynamic(..)
                | TyKind::Param(_)
                | TyKind::Bound(_, _)
                | TyKind::CoroutineWitness(_, _) => vec![],
                _ => todo!(),
            };
            for ty in field_tys {
                if let Err(mut tys) = ty_has_lifetimes_under_unsafe_ptr(ty, seen, ctxt) {
                    tys.push(ty);
                    return Err(tys);
                }
            }
            Ok(())
        }
        ty_has_lifetimes_under_unsafe_ptr(self.rust_ty(ctxt), &mut HashSet::default(), ctxt)
            .map_err(|tys| PlaceContainingPtrWithNestedLifetime {
                place: self,
                invalid_ty_chain: tys,
            })
    }

    #[must_use]
    pub fn prefix_place(&self) -> Option<Place<'tcx>> {
        let (prefix, _) = self.last_projection()?;
        Some(Place::new(prefix.local, prefix.projection))
    }

    /// The type of a MIR place is not necessarily determined by the syntactic projection
    /// elems from the root place: the projection elements may contain additional type information
    /// depending on how the place is used. Therefore, the same (syntactic) place may in fact
    /// be different due to the different types in its projection.
    ///
    /// This function converts the Place into a canonical form by re-projecting the place
    /// from its local, and using types derived from the root place as the types associated
    /// with Field region projections.
    #[must_use]
    pub fn with_inherent_region<'a>(self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> Self
    where
        'tcx: 'a,
    {
        let mut proj_iter = self.iter_projections(ctxt.ctxt()).into_iter();
        let mut place = if let Some((place, elem)) = proj_iter.next() {
            place.project_deeper(elem, ctxt).unwrap()
        } else {
            return self;
        };
        for (_, elem) in proj_iter {
            if let Ok(next_place) = place.project_deeper(elem, ctxt) {
                place = next_place;
            } else {
                // We cannot normalize the place (probably due to indexing of an
                // alias type that we cannot resolve). For now we just return the
                // original place.
                return self;
            }
        }
        place
    }

    pub fn is_mut_ref<'a>(&self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> bool
    where
        'tcx: 'a,
    {
        matches!(
            self.0.ty(ctxt.body(), ctxt.tcx()).ty.kind(),
            TyKind::Ref(_, _, Mutability::Mut)
        )
    }

    pub fn is_shared_ref<'a>(self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> bool
    where
        'tcx: 'a,
    {
        matches!(self.ref_mutability(ctxt), Some(Mutability::Not))
    }

    pub fn is_ref<'a>(self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> bool
    where
        'tcx: 'a,
    {
        self.0.ty(ctxt.body(), ctxt.tcx()).ty.is_ref()
    }

    pub fn ref_mutability<'a>(&self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> Option<Mutability>
    where
        'tcx: 'a,
    {
        self.0.ty(ctxt.body(), ctxt.tcx()).ty.ref_mutability()
    }

    #[must_use]
    pub fn common_prefix(self, other: Self) -> Self {
        assert_eq!(self.local, other.local);

        let max_len = std::cmp::min(self.projection.len(), other.projection.len());
        let common_prefix = self
            .compare_projections(other)
            .position(|(eq, _, _)| !eq)
            .unwrap_or(max_len);
        Self::new(self.local, &self.projection[..common_prefix])
    }

    #[must_use]
    pub fn joinable_to(self, to: Self) -> Self {
        assert!(self.is_prefix_of(to));
        let diff = to.projection.len() - self.projection.len();
        let to_proj = self.projection.len()
            + to.projection[self.projection.len()..]
                .iter()
                .position(|p| !matches!(p, ProjectionElem::Deref | ProjectionElem::Field(..)))
                .unwrap_or(diff);
        Self::new(self.local, &to.projection[..to_proj])
    }

    #[must_use]
    pub fn last_projection(self) -> Option<(Self, PlaceElem<'tcx>)> {
        self.0
            .last_projection()
            .map(|(place, proj)| (place.into(), proj))
    }

    #[must_use]
    pub fn last_projection_ty(self) -> Option<Ty<'tcx>> {
        self.last_projection().and_then(|(_, proj)| match proj {
            ProjectionElem::Field(_, ty) | ProjectionElem::OpaqueCast(ty) => Some(ty),
            _ => None,
        })
    }

    #[must_use]
    pub fn is_deref_of(self, other: Self) -> bool {
        self.projection.last() == Some(&ProjectionElem::Deref)
            && other.is_prefix_of(self)
            && other.projection.len() == self.projection.len() - 1
    }

    #[must_use]
    pub fn is_downcast_of(self, other: Self) -> Option<VariantIdx> {
        if let Some(ProjectionElem::Downcast(_, index)) = self.projection.last() {
            if other.is_prefix_of(self) && other.projection.len() == self.projection.len() - 1 {
                Some(*index)
            } else {
                None
            }
        } else {
            None
        }
    }

    pub(crate) fn iter_projections_after<'a>(
        self,
        other: Self,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Option<impl Iterator<Item = (Self, PlaceElem<'tcx>)>>
    where
        'tcx: 'a,
    {
        if other.is_prefix_of(self) {
            Some(
                self.iter_projections(ctxt.ctxt())
                    .into_iter()
                    .skip(other.projection.len()),
            )
        } else {
            None
        }
    }

    #[must_use]
    pub fn is_deref(self) -> bool {
        self.projection.last() == Some(&ProjectionElem::Deref)
    }

    #[must_use]
    pub fn target_place(self) -> Option<Self> {
        if let Some(ProjectionElem::Deref) = self.projection.last() {
            Some(Place::new(
                self.local,
                &self.projection[..self.projection.len() - 1],
            ))
        } else {
            None
        }
    }

    #[must_use]
    pub fn nearest_owned_place<'a>(self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> Self
    where
        'tcx: 'a,
    {
        if self.is_owned(ctxt) {
            return self;
        }
        for (place, _) in self.iter_projections(ctxt).into_iter().rev() {
            if place.is_owned(ctxt) {
                return place;
            }
        }
        unreachable!()
    }

    pub(crate) fn is_prefix_or_postfix_of(self, other: Self) -> bool {
        self.is_prefix_of(other) || other.is_prefix_of(self)
    }
}

impl Hash for Place<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.local.hash(state);
        let projection = self.0.projection;
        for &pe in projection {
            match pe {
                ProjectionElem::Field(field, _) => {
                    discriminant(&pe).hash(state);
                    field.hash(state);
                }
                ProjectionElem::Downcast(_, variant) => {
                    discriminant(&pe).hash(state);
                    variant.hash(state);
                }
                _ => pe.hash(state),
            }
        }
    }
}

impl<'tcx> From<PlaceRef<'tcx>> for Place<'tcx> {
    fn from(value: PlaceRef<'tcx>) -> Self {
        Self(value)
    }
}
impl<'tcx> From<MirPlace<'tcx>> for Place<'tcx> {
    fn from(value: MirPlace<'tcx>) -> Self {
        Self(value.as_ref())
    }
}
impl From<Local> for Place<'_> {
    fn from(value: Local) -> Self {
        MirPlace::from(value).into()
    }
}
