//! Data structures for lifetime projections.
use std::{borrow::Cow, fmt, hash::Hash, marker::PhantomData};

use derive_more::{Display, From};

use super::{
    borrow_pcg_edge::LocalNode, has_pcs_elem::LabelLifetimeProjection, visitor::extract_regions,
};
use crate::{
    borrow_pcg::{
        edge_data::LabelNodePredicate,
        graph::loop_abstraction::MaybeRemoteCurrentPlace,
        has_pcs_elem::{
            LabelLifetimeProjectionResult, LabelNodeContext, LabelPlaceWithContext, PlaceLabeller,
        },
    },
    error::PcgError,
    pcg::{LocalNodeLike, PcgNode, PcgNodeLike, PcgNodeType},
    rustc_interface::{
        index::{Idx, IndexVec},
        middle::{
            mir::{Const, Local, PlaceElem, interpret::Scalar},
            ty::{
                self, DebruijnIndex, RegionVid, TyKind, TypeSuperVisitable, TypeVisitable,
                TypeVisitor,
            },
        },
    },
    utils::{
        CompilerCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, HasPlace, HasTyCtxt, Place,
        PlaceProjectable, SnapshotLocation, VALIDITY_CHECKS_WARN_ONLY,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
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

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt> for RegionVid {
    fn display_output(&self, ctxt: Ctxt, _mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Text(
            if let Some(string) = ctxt.bc().override_region_debug_string(*self) {
                string.to_owned()
            } else {
                format!("{self:?}")
            }
            .into(),
        )
    }
}

impl std::fmt::Display for PcgRegion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.output(None, OutputMode::Normal).into_text())
    }
}

impl PcgRegion {
    pub fn is_static(self) -> bool {
        matches!(self, PcgRegion::ReStatic)
    }
    pub fn output(&self, ctxt: Option<CompilerCtxt<'_, '_>>, _mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Text(
            match self {
                PcgRegion::RegionVid(vid) => {
                    if let Some(ctxt) = ctxt {
                        vid.display_string(ctxt)
                    } else {
                        format!("{vid:?}")
                    }
                }
                PcgRegion::ReErased => "ReErased".to_owned(),
                PcgRegion::ReStatic => "ReStatic".to_owned(),
                PcgRegion::ReBound(debruijn_index, region) => {
                    format!("ReBound({debruijn_index:?}, {region:?})")
                }
                PcgRegion::ReLateParam(p) => format!("ReLateParam({p:?})"),
                PcgRegion::PcgInternalError(pcg_region_internal_error) => {
                    format!("{pcg_region_internal_error:?}")
                }
                PcgRegion::RePlaceholder(placeholder) => format!("RePlaceholder({placeholder:?})"),
                PcgRegion::ReEarlyParam(early_param_region) => {
                    format!("ReEarlyParam({early_param_region:?})")
                }
            }
            .into(),
        )
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

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt> for PcgRegion {
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        self.output(Some(ctxt.bc_ctxt()), mode)
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

/// The most general base of a lifetime projection. Either a [`MaybeRemotePlace`]
/// or a constant.
pub type PcgLifetimeProjectionBase<'tcx> = PlaceOrConst<'tcx, MaybeRemotePlace<'tcx>>;

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

impl<'tcx, Ctxt, T: HasTy<'tcx, Ctxt>> HasRegions<'tcx, Ctxt> for PlaceOrConst<'tcx, T> {
    fn regions(&self, ctxt: Ctxt) -> IndexVec<RegionIdx, PcgRegion> {
        extract_regions(self.rust_ty(ctxt))
    }
}

impl<'tcx, T, Ctxt: HasTyCtxt<'tcx>> DisplayWithCtxt<Ctxt> for PlaceOrConst<'tcx, T>
where
    T: DisplayWithCtxt<Ctxt>,
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        match self {
            PlaceOrConst::Place(p) => p.display_output(ctxt, mode),
            PlaceOrConst::Const(c) => c.display_output(ctxt, mode),
        }
    }
}

impl<'tcx, Ctxt: HasTyCtxt<'tcx>> DisplayWithCtxt<Ctxt> for Const<'tcx> {
    fn display_output(&self, _ctxt: Ctxt, _mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Text(format!("{self}").into())
    }
}

impl DisplayWithCtxt<()> for Scalar {
    fn display_output(&self, _ctxt: (), _mode: OutputMode) -> DisplayOutput {
        DisplayOutput::Text(format!("{self}").into())
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
        predicate: &LabelNodePredicate<'tcx>,
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

impl<'tcx> PcgLifetimeProjectionBaseLike<'tcx> for PcgLifetimeProjectionBase<'tcx> {
    fn to_pcg_lifetime_projection_base(&self) -> PcgLifetimeProjectionBase<'tcx> {
        *self
    }
}

impl<'tcx, T: PcgLifetimeProjectionBaseLike<'tcx>> PcgNodeLike<'tcx>
    for LifetimeProjection<'tcx, T>
{
    fn to_pcg_node<C: Copy>(self, _ctxt: CompilerCtxt<'_, 'tcx, C>) -> PcgNode<'tcx> {
        PcgNode::LifetimeProjection(self.with_base(self.base.to_pcg_lifetime_projection_base()))
    }

    fn node_type(&self) -> PcgNodeType {
        PcgNodeType::LifetimeProjection
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

impl DisplayWithCtxt<()> for LifetimeProjectionLabel {
    fn display_output(&self, ctxt: (), mode: OutputMode) -> DisplayOutput {
        match self {
            LifetimeProjectionLabel::Location(location) => location.display_output(ctxt, mode),
            LifetimeProjectionLabel::Future => DisplayOutput::Text(Cow::Borrowed("FUTURE")),
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
        predicate: &LabelNodePredicate<'tcx>,
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

impl<'a, 'tcx, P: Copy> LabelLifetimeProjection<'a, 'tcx> for LifetimeProjection<'tcx, P>
where
    P: PcgLifetimeProjectionBaseLike<'tcx>,
{
    fn label_lifetime_projection(
        &mut self,
        predicate: &LabelNodePredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        _ctxt: CompilerCtxt<'a, 'tcx>,
    ) -> LabelLifetimeProjectionResult {
        if predicate.applies_to(
            PcgNode::LifetimeProjection(
                self.with_base(self.base.to_pcg_lifetime_projection_base()),
            ),
            None,
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
    pub(crate) fn is_invariant_in_type<'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>>(
        &self,
        ctxt: Ctxt,
    ) -> bool
    where
        'tcx: 'a,
        T: HasTy<'tcx, Ctxt> + HasRegions<'tcx, Ctxt>,
    {
        region_is_invariant_in_type(
            ctxt.ctxt().tcx(),
            self.region(ctxt),
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
                Err("Const cannot be converted to a region projection".to_owned())
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
    fn to_local_node<C: Copy>(self, _ctxt: CompilerCtxt<'_, 'tcx, C>) -> LocalNode<'tcx> {
        LocalNode::LifetimeProjection(self)
    }
}

pub trait HasRegions<'tcx, Ctxt> {
    fn regions(&self, ctxt: Ctxt) -> IndexVec<RegionIdx, PcgRegion>;
    fn lifetime_projections<'a>(
        self,
        ctxt: Ctxt,
    ) -> IndexVec<RegionIdx, LifetimeProjection<'tcx, Self>>
    where
        'tcx: 'a,
        Self: Sized + Copy + std::fmt::Debug,
        Ctxt: HasCompilerCtxt<'a, 'tcx>,
    {
        self.regions(ctxt)
            .into_iter()
            .map(|region| LifetimeProjection::new(self, region, None, ctxt).unwrap())
            .collect()
    }
}

pub trait HasTy<'tcx, Ctxt> {
    fn rust_ty(&self, ctxt: Ctxt) -> ty::Ty<'tcx>;
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
    'a,
    'tcx: 'a,
    Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>,
    T: PcgLifetimeProjectionBaseLike<'tcx>
        + DisplayWithCtxt<Ctxt>
        + HasTy<'tcx, Ctxt>
        + HasRegions<'tcx, Ctxt>,
> DisplayWithCtxt<Ctxt> for LifetimeProjection<'tcx, T>
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        let label_part = match self.label {
            Some(label) => {
                DisplayOutput::Seq(vec![DisplayOutput::SPACE, label.display_output((), mode)])
            }
            _ => DisplayOutput::EMPTY,
        };
        DisplayOutput::Seq(vec![
            self.base.display_output(ctxt, mode),
            DisplayOutput::DOWN_ARROW,
            self.region(ctxt).display_output(ctxt.bc_ctxt(), mode),
            label_part,
        ])
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

impl<
    'a,
    'tcx: 'a,
    Ctxt: HasCompilerCtxt<'a, 'tcx>,
    T: HasPlace<'tcx>
        + PcgLifetimeProjectionBaseLike<'tcx>
        + PlaceProjectable<'tcx, Ctxt>
        + HasTy<'tcx, Ctxt>
        + HasRegions<'tcx, Ctxt>,
> PlaceProjectable<'tcx, Ctxt> for LifetimeProjection<'tcx, T>
{
    fn project_deeper(&self, elem: PlaceElem<'tcx>, ctxt: Ctxt) -> Result<Self, PcgError> {
        LifetimeProjection::new(
            self.base.project_deeper(elem, ctxt)?,
            self.region(ctxt),
            self.label,
            ctxt,
        )
        .ok_or_else(|| {
            PcgError::internal(format!(
                "Region {region} not found in place {base:?}",
                region = self.region(ctxt),
                base = self.base,
            ))
        })
    }

    fn iter_projections(&self, ctxt: Ctxt) -> Vec<(Self, PlaceElem<'tcx>)> {
        self.base
            .iter_projections(ctxt)
            .into_iter()
            .map(move |(base, elem)| {
                (
                    LifetimeProjection::new(base, self.region(ctxt), self.label, ctxt)
                        .unwrap_or_else(|| {
                            panic!(
                               "Error iter projections for {:?}: Place ty {:?} does not have region {:?}",
                                self,
                                base.place().ty(ctxt),
                                self.region(ctxt),
                            );
                        }),
                    elem,
                )
            })
            .collect()
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

    fn is_place(&self) -> bool {
        false
    }
}

impl<
    'a,
    'tcx: 'a,
    T: HasTy<'tcx, CompilerCtxt<'a, 'tcx>>
        + HasRegions<'tcx, CompilerCtxt<'a, 'tcx>>
        + PcgLifetimeProjectionBaseLike<'tcx>,
> HasValidityCheck<'a, 'tcx> for LifetimeProjection<'tcx, T>
{
    fn check_validity(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> Result<(), String> {
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
    pub fn new<'a, Ctxt>(
        base: T,
        region: PcgRegion,
        label: Option<LifetimeProjectionLabel>,
        ctxt: Ctxt,
    ) -> Option<Self>
    where
        'tcx: 'a,
        T: HasRegions<'tcx, Ctxt>,
    {
        let region_idx = base
            .regions(ctxt)
            .into_iter_enumerated()
            .find(|(_, r)| *r == region)?
            .0;

        let result = Self {
            base,
            region_idx,
            label,
            phantom: PhantomData,
        };
        Some(result)
    }
}

impl<'tcx, T> LifetimeProjection<'tcx, T> {
    pub fn region<'a, Ctxt>(&self, ctxt: Ctxt) -> PcgRegion
    where
        'tcx: 'a,
        T: HasRegions<'tcx, Ctxt>,
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
        predicate: &LabelNodePredicate<'tcx>,
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
