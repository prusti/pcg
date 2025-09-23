//! Data structures for lifetime projections.
use std::{fmt, hash::Hash, marker::PhantomData};

use derive_more::{Display, From};
use serde_json::json;

use super::{
    borrow_pcg_edge::LocalNode, has_pcs_elem::LabelLifetimeProjection, visitor::extract_regions,
};
use crate::{
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::{
        edge_data::LabelPlacePredicate,
        graph::loop_abstraction::MaybeRemoteCurrentPlace,
        has_pcs_elem::{
            LabelLifetimeProjectionPredicate, LabelLifetimeProjectionResult, LabelNodeContext,
            LabelPlaceWithContext, PlaceLabeller,
        },
    },
    error::{PcgError, PcgInternalError},
    pcg::{LocalNodeLike, PcgNode, PcgNodeLike},
    rustc_interface::{
        index::{Idx, IndexVec},
        middle::{
            mir::{Const, Local, PlaceElem},
            ty::{
                self, DebruijnIndex, RegionVid, TyKind, TypeSuperVisitable, TypeVisitable,
                TypeVisitor,
            },
        },
    },
    utils::{
        CompilerCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, HasPlace, Place, PlaceProjectable,
        SnapshotLocation, VALIDITY_CHECKS_WARN_ONLY,
        display::DisplayWithCompilerCtxt,
        json::ToJsonWithCompilerCtxt,
        place::{maybe_old::MaybeLabelledPlace, maybe_remote::MaybeRemotePlace},
        remote::RemotePlace,
        validity::HasValidityCheck,
    },
};

/// A region occuring in region projections
#[derive(PartialEq, Eq, Clone, Copy, Hash, From, Debug)]
pub enum PcgRegion {
    RegionVid(RegionVid),
    ReErased,
    ReStatic,
    RePlaceholder(ty::PlaceholderRegion),
    ReBound(DebruijnIndex, ty::BoundRegion),
    ReLateParam(ty::LateParamRegion),
    PcgInternalError(PcgRegionInternalError),
    ReEarlyParam(ty::EarlyParamRegion),
}

#[derive(PartialEq, Eq, Clone, Copy, Hash, From, Debug)]
pub enum PcgRegionInternalError {
    RegionIndexOutOfBounds(RegionIdx),
}

impl<'tcx> DisplayWithCompilerCtxt<'tcx, &dyn BorrowCheckerInterface<'tcx>> for RegionVid {
    fn to_short_string(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
        if let Some(string) = ctxt.bc.override_region_debug_string(*self) {
            string.to_string()
        } else {
            format!("{self:?}")
        }
    }
}

impl std::fmt::Display for PcgRegion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_string(None))
    }
}

impl PcgRegion {
    pub fn is_static(self) -> bool {
        matches!(self, PcgRegion::ReStatic)
    }
    pub fn to_string(&self, ctxt: Option<CompilerCtxt<'_, '_>>) -> String {
        match self {
            PcgRegion::RegionVid(vid) => {
                if let Some(ctxt) = ctxt {
                    vid.to_short_string(ctxt)
                } else {
                    format!("{vid:?}")
                }
            }
            PcgRegion::ReErased => "ReErased".to_string(),
            PcgRegion::ReStatic => "ReStatic".to_string(),
            PcgRegion::ReBound(debruijn_index, region) => {
                format!("ReBound({debruijn_index:?}, {region:?})")
            }
            PcgRegion::ReLateParam(_) => todo!(),
            PcgRegion::PcgInternalError(pcg_region_internal_error) => {
                format!("{pcg_region_internal_error:?}")
            }
            PcgRegion::RePlaceholder(placeholder) => format!("RePlaceholder({placeholder:?})"),
            PcgRegion::ReEarlyParam(early_param_region) => {
                format!("ReEarlyParam({early_param_region:?})")
            }
        }
    }

    pub fn vid(&self) -> Option<RegionVid> {
        match self {
            PcgRegion::RegionVid(vid) => Some(*vid),
            _ => None,
        }
    }

    pub(crate) fn rust_region<'a, 'tcx: 'a>(self, ctxt: ty::TyCtxt<'tcx>) -> ty::Region<'tcx> {
        #[rustversion::before(2025-03-01)]
        fn new_late_param<'a, 'tcx: 'a>(
            late_param_region: ty::LateParamRegion,
            ctxt: ty::TyCtxt<'tcx>,
        ) -> ty::Region<'tcx> {
            ty::Region::new_late_param(
                ctxt,
                late_param_region.scope,
                late_param_region.bound_region,
            )
        }
        #[rustversion::since(2025-03-01)]
        fn new_late_param<'a, 'tcx: 'a>(
            late_param_region: ty::LateParamRegion,
            ctxt: ty::TyCtxt<'tcx>,
        ) -> ty::Region<'tcx> {
            ty::Region::new_late_param(ctxt, late_param_region.scope, late_param_region.kind)
        }
        match self {
            PcgRegion::RegionVid(region_vid) => ty::Region::new_var(ctxt, region_vid),
            PcgRegion::ReErased => todo!(),
            PcgRegion::ReStatic => ctxt.lifetimes.re_static,
            PcgRegion::RePlaceholder(_) => todo!(),
            PcgRegion::ReBound(debruijn_index, bound_region) => {
                ty::Region::new_bound(ctxt, debruijn_index, bound_region)
            }
            PcgRegion::ReLateParam(late_param_region) => new_late_param(late_param_region, ctxt),
            PcgRegion::PcgInternalError(_) => todo!(),
            PcgRegion::ReEarlyParam(early_param_region) => {
                ty::Region::new_early_param(ctxt, early_param_region)
            }
        }
    }
}

impl<'tcx, 'a> DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>> for PcgRegion {
    fn to_short_string(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
        self.to_string(Some(ctxt))
    }
}

impl<'tcx> From<ty::Region<'tcx>> for PcgRegion {
    fn from(region: ty::Region<'tcx>) -> Self {
        match region.kind() {
            ty::RegionKind::ReVar(vid) => PcgRegion::RegionVid(vid),
            ty::RegionKind::ReErased => PcgRegion::ReErased,
            ty::RegionKind::ReEarlyParam(p) => PcgRegion::ReEarlyParam(p),
            ty::RegionKind::ReBound(debruijn_index, inner) => {
                PcgRegion::ReBound(debruijn_index, inner)
            }
            ty::RegionKind::ReLateParam(late_param) => PcgRegion::ReLateParam(late_param),
            ty::RegionKind::ReStatic => PcgRegion::ReStatic,
            ty::RegionKind::RePlaceholder(r) => PcgRegion::RePlaceholder(r),
            ty::RegionKind::ReError(_) => todo!(),
        }
    }
}

/// The index of a region within a type.
///
/// For example is `a` has type `A<'t>` and `b` has type `B<'u>`,
/// an assignment e.g. `b = move a` will have region projections from `b`
/// to `u`
#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, Ord, PartialOrd, From)]
pub struct RegionIdx(usize);

impl Idx for RegionIdx {
    fn new(idx: usize) -> Self {
        RegionIdx(idx)
    }

    fn index(self) -> usize {
        self.0
    }
}

pub type PcgLifetimeProjectionBase<'tcx> = PlaceOrConst<'tcx, MaybeRemotePlace<'tcx>>;

/// The most general base of a lifetime projection. Either a [`MaybeRemotePlace`]
/// or a constant.
#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, Display)]
pub enum PlaceOrConst<'tcx, T> {
    Place(T),
    Const(Const<'tcx>),
}

impl<'tcx, Ctxt, T: HasTy<'tcx, Ctxt>> HasTy<'tcx, Ctxt> for PlaceOrConst<'tcx, T> {
    fn rust_ty(&self, ctxt: Ctxt) -> ty::Ty<'tcx> {
        match self {
            PlaceOrConst::Place(p) => p.rust_ty(ctxt),
            PlaceOrConst::Const(c) => c.ty(),
        }
    }
}

impl<'tcx, 'a, T: DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>>
    DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>> for PlaceOrConst<'tcx, T>
{
    fn to_short_string(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
        match self {
            PlaceOrConst::Place(p) => p.to_short_string(ctxt),
            PlaceOrConst::Const(c) => format!("Const({c:?})"),
        }
    }
}

impl<'tcx> From<Place<'tcx>> for PlaceOrConst<'tcx, MaybeRemotePlace<'tcx>> {
    fn from(place: Place<'tcx>) -> Self {
        PlaceOrConst::Place(place.into())
    }
}

impl<'tcx, T> PlaceOrConst<'tcx, T> {
    pub(crate) fn expect_place(self) -> T {
        match self {
            PlaceOrConst::Place(p) => p,
            PlaceOrConst::Const(_) => todo!(),
        }
    }

    pub(crate) fn map_place<U>(self, f: impl FnOnce(T) -> U) -> PlaceOrConst<'tcx, U> {
        match self {
            PlaceOrConst::Place(p) => PlaceOrConst::Place(f(p)),
            PlaceOrConst::Const(c) => PlaceOrConst::Const(c),
        }
    }

    pub(crate) fn mut_place<U>(&mut self, f: impl FnOnce(&mut T) -> U) -> Option<U> {
        match self {
            PlaceOrConst::Place(p) => Some(f(p)),
            PlaceOrConst::Const(_) => None,
        }
    }
}

impl<'tcx, U, T: LabelPlaceWithContext<'tcx, U>> LabelPlaceWithContext<'tcx, U>
    for PlaceOrConst<'tcx, T>
{
    fn label_place_with_context(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        label_context: U,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.mut_place(|p| p.label_place_with_context(predicate, labeller, label_context, ctxt))
            .unwrap_or(false)
    }
}

impl<'tcx> PcgLifetimeProjectionBase<'tcx> {
    pub(crate) fn maybe_remote_current_place(&self) -> Option<MaybeRemoteCurrentPlace<'tcx>> {
        match self {
            PlaceOrConst::Place(p) => p.maybe_remote_current_place(),
            PlaceOrConst::Const(_) => None,
        }
    }
    pub(crate) fn is_mutable<'a>(&self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> bool
    where
        'tcx: 'a,
    {
        match self {
            PlaceOrConst::Place(p) => p.is_mutable(ctxt),
            PlaceOrConst::Const(_) => false,
        }
    }
    pub(crate) fn base_ty<'a>(self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> ty::Ty<'tcx>
    where
        'tcx: 'a,
    {
        match self {
            PlaceOrConst::Place(maybe_remote_place) => {
                let local_place: Place<'tcx> =
                    maybe_remote_place.related_local_place().local.into();
                local_place.ty(ctxt).ty
            }
            PlaceOrConst::Const(c) => c.ty(),
        }
    }
    pub(crate) fn as_local_place_mut(&mut self) -> Option<&mut MaybeLabelledPlace<'tcx>> {
        match self {
            PlaceOrConst::Place(p) => p.as_local_place_mut(),
            PlaceOrConst::Const(_) => None,
        }
    }

    pub(crate) fn as_local_place(&self) -> Option<MaybeLabelledPlace<'tcx>> {
        match self {
            PlaceOrConst::Place(p) => p.as_local_place(),
            PlaceOrConst::Const(_) => None,
        }
    }
    pub(crate) fn as_current_place(&self) -> Option<Place<'tcx>> {
        match self {
            PlaceOrConst::Place(p) => p.as_current_place(),
            PlaceOrConst::Const(_) => None,
        }
    }
}
impl<'tcx> HasValidityCheck<'_, 'tcx> for PcgLifetimeProjectionBase<'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        match self {
            PlaceOrConst::Place(p) => p.check_validity(ctxt),
            PlaceOrConst::Const(_) => todo!(),
        }
    }
}

impl<'tcx, 'a> ToJsonWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for PcgLifetimeProjectionBase<'tcx>
{
    fn to_json(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> serde_json::Value {
        match self {
            PlaceOrConst::Place(p) => p.to_json(ctxt),
            PlaceOrConst::Const(_) => todo!(),
        }
    }
}

impl<'tcx> PcgLifetimeProjectionBaseLike<'tcx> for PcgLifetimeProjectionBase<'tcx> {
    fn to_pcg_lifetime_projection_base(&self) -> PcgLifetimeProjectionBase<'tcx> {
        *self
    }
}

impl<'tcx, T: PcgLifetimeProjectionBaseLike<'tcx>> PcgNodeLike<'tcx>
    for LifetimeProjection<'tcx, T>
{
    fn to_pcg_node<C: Copy>(self, _ctxt: CompilerCtxt<'_, 'tcx, C>) -> PcgNode<'tcx> {
        self.with_base(self.base.to_pcg_lifetime_projection_base())
            .into()
    }
}

#[deprecated(note = "Use LifetimeProjectionLabel instead")]
pub type RegionProjectionLabel = LifetimeProjectionLabel;

/// A lifetime projection label. A label can be either a [`SnapshotLocation`] or
/// a special "Placeholder" label.
///
/// If a lifetime projection is labelled with a location, it corresponds to the
/// memory of the projection at that point.
///
/// If it's labelled with the "Placeholder" label, it represents the memory that
/// the projection will refer to once it becomes accessible.
///
#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, Ord, PartialOrd, From)]
pub enum LifetimeProjectionLabel {
    Location(SnapshotLocation),
    Future,
}

impl std::fmt::Display for LifetimeProjectionLabel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LifetimeProjectionLabel::Location(location) => write!(f, "{location}"),
            LifetimeProjectionLabel::Future => write!(f, "FUTURE"),
        }
    }
}

#[deprecated(note = "Use LifetimeProjection instead")]
pub type RegionProjection<'tcx, P = PcgLifetimeProjectionBase<'tcx>> = LifetimeProjection<'tcx, P>;

/// A lifetime projection b↓r, where `b` is a base and `r` is a region.
#[derive(PartialEq, Eq, Clone, Debug, Hash, Copy, Ord, PartialOrd)]
pub struct LifetimeProjection<'tcx, P = PcgLifetimeProjectionBase<'tcx>> {
    pub(crate) base: P,
    pub(crate) region_idx: RegionIdx,
    pub(crate) label: Option<LifetimeProjectionLabel>,
    phantom: PhantomData<&'tcx ()>,
}

pub(crate) trait PcgLifetimeProjectionLike<'tcx> {
    fn to_pcg_lifetime_projection(self) -> LifetimeProjection<'tcx>;
}

impl<'tcx> LabelPlaceWithContext<'tcx, LabelNodeContext> for LifetimeProjection<'tcx> {
    fn label_place_with_context(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        label_context: LabelNodeContext,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        if let Some(p) = self.base.as_local_place_mut() {
            p.label_place_with_context(predicate, labeller, label_context, ctxt)
        } else {
            false
        }
    }
}

impl<P> LifetimeProjection<'_, P> {
    pub(crate) fn is_future(&self) -> bool {
        self.label == Some(LifetimeProjectionLabel::Future)
    }
    pub(crate) fn label(&self) -> Option<LifetimeProjectionLabel> {
        self.label
    }
}

impl<'tcx> From<LifetimeProjection<'tcx, Place<'tcx>>> for LifetimeProjection<'tcx> {
    fn from(rp: LifetimeProjection<'tcx, Place<'tcx>>) -> Self {
        LifetimeProjection {
            base: rp.base.into(),
            region_idx: rp.region_idx,
            label: rp.label,
            phantom: PhantomData,
        }
    }
}

impl<'tcx, T, P> TryFrom<PcgNode<'tcx, T, P>> for LifetimeProjection<'tcx, P> {
    type Error = ();
    fn try_from(node: PcgNode<'tcx, T, P>) -> Result<Self, Self::Error> {
        match node {
            PcgNode::LifetimeProjection(rp) => Ok(rp),
            _ => Err(()),
        }
    }
}

impl<'tcx, P: Copy> LabelLifetimeProjection<'tcx> for LifetimeProjection<'tcx, P>
where
    P: PcgLifetimeProjectionBaseLike<'tcx>,
{
    fn label_lifetime_projection(
        &mut self,
        predicate: &LabelLifetimeProjectionPredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> LabelLifetimeProjectionResult {
        if predicate.matches(
            self.with_base(self.base.to_pcg_lifetime_projection_base()),
            ctxt,
        ) {
            self.label = label;
            LabelLifetimeProjectionResult::Changed
        } else {
            LabelLifetimeProjectionResult::Unchanged
        }
    }
}

impl<'tcx> From<LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>>
    for LifetimeProjection<'tcx, MaybeRemotePlace<'tcx>>
{
    fn from(value: LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>) -> Self {
        LifetimeProjection {
            base: value.base.into(),
            region_idx: value.region_idx,
            label: value.label,
            phantom: PhantomData,
        }
    }
}

pub(crate) struct TyVarianceVisitor<'tcx> {
    pub(crate) tcx: ty::TyCtxt<'tcx>,
    pub(crate) target: PcgRegion,
    pub(crate) found: bool,
}

impl<'tcx> TypeVisitor<ty::TyCtxt<'tcx>> for TyVarianceVisitor<'tcx> {
    fn visit_ty(&mut self, t: ty::Ty<'tcx>) {
        if self.found {
            return;
        }
        match t.kind() {
            TyKind::Adt(def_id, substs) => {
                let variances = self.tcx.variances_of(def_id.did());
                for (idx, region) in substs.regions().enumerate() {
                    if self.target == region.into()
                        && variances.get(idx) == Some(&ty::Variance::Invariant)
                    {
                        self.found = true;
                    }
                }
            }
            TyKind::RawPtr(ty, mutbl) | TyKind::Ref(_, ty, mutbl) => {
                if mutbl.is_mut() && extract_regions(*ty).iter().any(|r| self.target == *r) {
                    self.found = true;
                }
                // Otherwise, this is an immutable reference, don't check under
                // here since nothing will be mutable
            }
            _ => {
                t.super_visit_with(self);
            }
        }
    }
}

pub(crate) fn region_is_invariant_in_type<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    region: PcgRegion,
    ty: ty::Ty<'tcx>,
) -> bool {
    let mut visitor = TyVarianceVisitor {
        tcx,
        target: region,
        found: false,
    };
    ty.visit_with(&mut visitor);
    visitor.found
}

impl<'tcx, T: PcgLifetimeProjectionBaseLike<'tcx>> LifetimeProjection<'tcx, T> {
    pub(crate) fn is_invariant_in_type<'a>(&self, ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>) -> bool
    where
        'tcx: 'a,
    {
        region_is_invariant_in_type(
            ctxt.ctxt().tcx(),
            self.region(ctxt.ctxt()),
            self.base.to_pcg_lifetime_projection_base().base_ty(ctxt),
        )
    }
}

impl<'tcx, T: PcgLifetimeProjectionBaseLike<'tcx>> LifetimeProjection<'tcx, T> {
    #[must_use]
    pub(crate) fn with_placeholder_label<'a>(
        self,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> LifetimeProjection<'tcx, T>
    where
        'tcx: 'a,
    {
        self.with_label(Some(LifetimeProjectionLabel::Future), ctxt)
    }

    #[must_use]
    pub(crate) fn with_label<'a>(
        self,
        label: Option<LifetimeProjectionLabel>,
        _ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> LifetimeProjection<'tcx, T>
    where
        'tcx: 'a,
    {
        LifetimeProjection {
            base: self.base,
            region_idx: self.region_idx,
            label,
            phantom: PhantomData,
        }
    }
}
impl<'tcx> From<LifetimeProjection<'tcx, MaybeRemotePlace<'tcx>>> for LifetimeProjection<'tcx> {
    fn from(rp: LifetimeProjection<'tcx, MaybeRemotePlace<'tcx>>) -> Self {
        LifetimeProjection {
            base: PlaceOrConst::Place(rp.base),
            region_idx: rp.region_idx,
            label: rp.label,
            phantom: PhantomData,
        }
    }
}

impl<'tcx> TryFrom<LifetimeProjection<'tcx>> for LifetimeProjection<'tcx, MaybeRemotePlace<'tcx>> {
    type Error = ();
    fn try_from(rp: LifetimeProjection<'tcx>) -> Result<Self, Self::Error> {
        match rp.base {
            PlaceOrConst::Place(p) => Ok(LifetimeProjection {
                base: p,
                region_idx: rp.region_idx,
                label: rp.label,
                phantom: PhantomData,
            }),
            PlaceOrConst::Const(_) => Err(()),
        }
    }
}

impl<'tcx> TryFrom<LifetimeProjection<'tcx>>
    for LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>
{
    type Error = String;
    fn try_from(rp: LifetimeProjection<'tcx>) -> Result<Self, Self::Error> {
        match rp.base {
            PlaceOrConst::Place(p) => Ok(LifetimeProjection {
                base: p.try_into()?,
                region_idx: rp.region_idx,
                label: rp.label,
                phantom: PhantomData,
            }),
            PlaceOrConst::Const(_) => {
                Err("Const cannot be converted to a region projection".to_string())
            }
        }
    }
}

impl<'tcx> LocalNodeLike<'tcx> for LifetimeProjection<'tcx, Place<'tcx>> {
    fn to_local_node<C: Copy>(self, _ctxt: CompilerCtxt<'_, 'tcx, C>) -> LocalNode<'tcx> {
        LocalNode::LifetimeProjection(self.with_base(MaybeLabelledPlace::Current(self.base)))
    }
}

impl<'tcx> LocalNodeLike<'tcx> for LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>> {
    fn to_local_node<C: Copy>(self, _repacker: CompilerCtxt<'_, 'tcx, C>) -> LocalNode<'tcx> {
        LocalNode::LifetimeProjection(self)
    }
}

pub trait HasTy<'tcx, Ctxt> {
    fn rust_ty(&self, ctxt: Ctxt) -> ty::Ty<'tcx>;

    fn regions(&self, ctxt: Ctxt) -> IndexVec<RegionIdx, PcgRegion> {
        extract_regions(self.rust_ty(ctxt))
    }

    fn lifetime_projections<'a>(
        self,
        ctxt: Ctxt,
    ) -> IndexVec<RegionIdx, LifetimeProjection<'tcx, Self>>
    where
        Self: Sized + Copy + std::fmt::Debug,
        Ctxt: HasCompilerCtxt<'a, 'tcx>,
    {
        self.regions(ctxt)
            .into_iter()
            .map(|region| LifetimeProjection::new(region, self, None, ctxt).unwrap())
            .collect()
    }
}

/// Something that can be converted to a [`PcgLifetimeProjectionBase`].
pub trait PcgLifetimeProjectionBaseLike<'tcx>:
    Copy + std::fmt::Debug + std::hash::Hash + Eq + PartialEq
{
    fn to_pcg_lifetime_projection_base(&self) -> PcgLifetimeProjectionBase<'tcx>;
}

impl<'tcx> PcgLifetimeProjectionBaseLike<'tcx> for LocalLifetimeProjectionBase<'tcx> {
    fn to_pcg_lifetime_projection_base(&self) -> PcgLifetimeProjectionBase<'tcx> {
        PlaceOrConst::Place((*self).into())
    }
}

impl<'tcx> PcgLifetimeProjectionBaseLike<'tcx> for PlaceOrConst<'tcx, MaybeLabelledPlace<'tcx>> {
    fn to_pcg_lifetime_projection_base(&self) -> PcgLifetimeProjectionBase<'tcx> {
        self.map_place(Into::into)
    }
}

impl<
    'tcx,
    'a,
    T: PcgLifetimeProjectionBaseLike<'tcx>
        + DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
> DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for LifetimeProjection<'tcx, T>
{
    fn to_short_string(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
        let label_part = match self.label {
            Some(LifetimeProjectionLabel::Location(location)) => format!(" {location}"),
            Some(LifetimeProjectionLabel::Future) => " FUTURE".to_string(),
            _ => "".to_string(),
        };
        format!(
            "{}↓{}{}",
            self.base.to_short_string(ctxt),
            self.region(ctxt).to_short_string(ctxt),
            label_part
        )
    }
}

impl<
    'tcx,
    'a,
    T: PcgLifetimeProjectionBaseLike<'tcx>
        + ToJsonWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
> ToJsonWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for LifetimeProjection<'tcx, T>
{
    fn to_json(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> serde_json::Value {
        json!({
            "place": self.base.to_json(ctxt),
            "region": self.region(ctxt).to_string(Some(ctxt)),
        })
    }
}

impl<T: std::fmt::Display> fmt::Display for LifetimeProjection<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}↓{:?}", self.base, self.region_idx)
    }
}

impl<'tcx> From<LifetimeProjection<'tcx, Place<'tcx>>>
    for LifetimeProjection<'tcx, MaybeRemotePlace<'tcx>>
{
    fn from(rp: LifetimeProjection<'tcx, Place<'tcx>>) -> Self {
        LifetimeProjection {
            base: rp.base.into(),
            region_idx: rp.region_idx,
            label: rp.label,
            phantom: PhantomData,
        }
    }
}

impl<'tcx> TryFrom<LifetimeProjection<'tcx, MaybeRemotePlace<'tcx>>>
    for LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>
{
    type Error = String;
    fn try_from(rp: LifetimeProjection<'tcx, MaybeRemotePlace<'tcx>>) -> Result<Self, Self::Error> {
        Ok(LifetimeProjection {
            base: rp.base.try_into()?,
            region_idx: rp.region_idx,
            label: rp.label,
            phantom: PhantomData,
        })
    }
}

impl<'tcx> From<MaybeLabelledPlace<'tcx>> for PcgLifetimeProjectionBase<'tcx> {
    fn from(place: MaybeLabelledPlace<'tcx>) -> Self {
        PlaceOrConst::Place(place.into())
    }
}

impl<'tcx> From<LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>> for LifetimeProjection<'tcx> {
    fn from(rp: LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>) -> Self {
        LifetimeProjection {
            base: rp.base.into(),
            region_idx: rp.region_idx,
            label: rp.label,
            phantom: PhantomData,
        }
    }
}

impl<'tcx> From<LifetimeProjection<'tcx, Place<'tcx>>>
    for LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>
{
    fn from(rp: LifetimeProjection<'tcx, Place<'tcx>>) -> Self {
        LifetimeProjection {
            base: rp.base.into(),
            region_idx: rp.region_idx,
            label: rp.label,
            phantom: PhantomData,
        }
    }
}

impl<'tcx, T: PcgLifetimeProjectionBaseLike<'tcx> + PlaceProjectable<'tcx>> PlaceProjectable<'tcx>
    for LifetimeProjection<'tcx, T>
{
    fn project_deeper<'a>(
        &self,
        elem: PlaceElem<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Result<Self, PcgError> {
        LifetimeProjection::new(
            self.region(ctxt),
            self.base.project_deeper(elem, ctxt)?,
            self.label,
            ctxt,
        )
        .map_err(|e| e.into())
    }
}

impl<'tcx, T: PcgLifetimeProjectionBaseLike<'tcx> + HasPlace<'tcx>> HasPlace<'tcx>
    for LifetimeProjection<'tcx, T>
{
    fn place(&self) -> Place<'tcx> {
        self.base.place()
    }

    fn place_mut(&mut self) -> &mut Place<'tcx> {
        self.base.place_mut()
    }

    fn iter_projections<C: Copy>(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, C>,
    ) -> Vec<(Self, PlaceElem<'tcx>)> {
        self.base
            .iter_projections(ctxt)
            .into_iter()
            .map(move |(base, elem)| {
                (
                    LifetimeProjection::new(self.region(ctxt), base, self.label, ctxt)
                        .unwrap_or_else(|e| {
                            panic!(
                                "Error iter projections for {:?}: {:?}. Place ty: {:?}",
                                self,
                                e,
                                base.place().ty(ctxt),
                            );
                        }),
                    elem,
                )
            })
            .collect()
    }

    fn is_place(&self) -> bool {
        false
    }
}

impl<'tcx, T: PcgLifetimeProjectionBaseLike<'tcx>> HasValidityCheck<'_, 'tcx>
    for LifetimeProjection<'tcx, T>
{
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        let num_regions = self.base.regions(ctxt);
        if self.region_idx.index() >= num_regions.len() {
            Err(format!(
                "Region index {} is out of bounds for place {:?}:{:?}",
                self.region_idx.index(),
                self.base,
                self.base.rust_ty(ctxt)
            ))
        } else {
            Ok(())
        }
    }
}

impl<'tcx, T> LifetimeProjection<'tcx, T> {
    pub(crate) fn from_index(base: T, region_idx: RegionIdx) -> Self {
        Self {
            base,
            region_idx,
            label: None,
            phantom: PhantomData,
        }
    }
}

impl<'tcx, T: std::fmt::Debug> LifetimeProjection<'tcx, T> {
    pub(crate) fn new<'a, Ctxt: HasCompilerCtxt<'a, 'tcx>>(
        region: PcgRegion,
        base: T,
        label: Option<LifetimeProjectionLabel>,
        ctxt: Ctxt,
    ) -> Result<Self, PcgInternalError>
    where
        'tcx: 'a,
        T: HasTy<'tcx, Ctxt>,
    {
        let region_idx = base
            .regions(ctxt)
            .into_iter_enumerated()
            .find(|(_, r)| *r == region)
            .map(|(idx, _)| idx);
        let region_idx = match region_idx {
            Some(region_idx) => region_idx,
            None => {
                return Err(PcgInternalError::new(format!(
                    "Region {region} not found in place {base:?}"
                )));
            }
        };

        let result = Self {
            base,
            region_idx,
            label,
            phantom: PhantomData,
        };
        Ok(result)
    }
}

impl<'tcx, T> LifetimeProjection<'tcx, T> {
    pub(crate) fn region<'a>(&self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> PcgRegion
    where
        'tcx: 'a,
        T: HasTy<'tcx>,
    {
        let regions = self.base.regions(ctxt);
        if self.region_idx.index() >= regions.len() {
            if *VALIDITY_CHECKS_WARN_ONLY {
                PcgRegion::PcgInternalError(PcgRegionInternalError::RegionIndexOutOfBounds(
                    self.region_idx,
                ))
            } else {
                unreachable!()
            }
        } else {
            regions[self.region_idx]
        }
    }
}

impl<T: Copy> LifetimeProjection<'_, T> {
    pub fn base(&self) -> T {
        self.base
    }
}

impl<'tcx, T> LifetimeProjection<'tcx, T> {
    pub(crate) fn place_mut(&mut self) -> &mut T {
        &mut self.base
    }

    pub(crate) fn rebase<U: PcgLifetimeProjectionBaseLike<'tcx> + From<T>>(
        self,
    ) -> LifetimeProjection<'tcx, U>
    where
        T: Copy,
    {
        self.with_base(self.base.into())
    }

    pub fn with_base<U>(self, base: U) -> LifetimeProjection<'tcx, U> {
        LifetimeProjection {
            base,
            region_idx: self.region_idx,
            label: self.label,
            phantom: PhantomData,
        }
    }
}

impl<'tcx> LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>> {
    /// If the region projection is of the form `x↓'a` and `x` has type `&'a T` or `&'a mut T`,
    /// this returns `*x`.
    pub fn deref(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Option<MaybeLabelledPlace<'tcx>> {
        if self.base.ty_region(ctxt) == Some(self.region(ctxt)) {
            Some(self.base.project_deref(ctxt))
        } else {
            None
        }
    }
}

pub(crate) type LocalLifetimeProjectionBase<'tcx> = MaybeLabelledPlace<'tcx>;

pub(crate) type LocalLifetimeProjection<'tcx> =
    LifetimeProjection<'tcx, LocalLifetimeProjectionBase<'tcx>>;

impl<'tcx> LocalLifetimeProjection<'tcx> {
    pub fn to_lifetime_projection(&self) -> LifetimeProjection<'tcx> {
        self.with_base(self.base.into())
    }

    pub fn local(&self) -> Local {
        self.base.local()
    }
}

impl<'tcx> LabelPlaceWithContext<'tcx, LabelNodeContext> for LocalLifetimeProjection<'tcx> {
    fn label_place_with_context(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        label_context: LabelNodeContext,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.base
            .label_place_with_context(predicate, labeller, label_context, ctxt)
    }
}

impl<'tcx> LifetimeProjection<'tcx> {
    fn as_local_region_projection(
        &self,
    ) -> Option<LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>> {
        match self.base {
            PlaceOrConst::Place(maybe_remote_place) => match maybe_remote_place {
                MaybeRemotePlace::Local(local) => Some(self.with_base(local)),
                _ => None,
            },
            PlaceOrConst::Const(_) => None,
        }
    }

    /// If the region projection is of the form `x↓'a` and `x` has type `&'a T` or `&'a mut T`,
    /// this returns `*x`. Otherwise, it returns `None`.
    pub fn deref(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Option<MaybeLabelledPlace<'tcx>> {
        self.as_local_region_projection()
            .and_then(|rp| rp.deref(ctxt))
    }
}

impl From<RemotePlace> for PcgLifetimeProjectionBase<'_> {
    fn from(remote_place: RemotePlace) -> Self {
        PlaceOrConst::Place(remote_place.into())
    }
}
