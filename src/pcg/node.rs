use crate::{
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::{
        borrow_pcg_edge::LocalNode,
        domain::LoopAbstractionInput,
        edge_data::LabelPlacePredicate,
        graph::loop_abstraction::MaybeRemoteCurrentPlace,
        has_pcs_elem::{
            LabelLifetimeProjection, LabelLifetimeProjectionPredicate,
            LabelLifetimeProjectionResult, LabelPlaceWithContext, PlaceLabeller,
        },
        region_projection::{
            LifetimeProjection, LifetimeProjectionLabel, PcgLifetimeProjectionBase,
            PcgLifetimeProjectionBaseLike, PlaceOrConst,
        },
    },
    rustc_interface::middle::mir,
    utils::{
        CompilerCtxt, HasCompilerCtxt, Place, SnapshotLocation, display::DisplayWithCompilerCtxt,
        json::ToJsonWithCompilerCtxt, maybe_old::MaybeLabelledPlace,
        place::maybe_remote::MaybeRemotePlace, remote::RemotePlace, validity::HasValidityCheck,
    },
};

#[deprecated(note = "Use `PcgNode` instead")]
pub type PCGNode<'tcx> = PcgNode<'tcx>;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum PcgNode<'tcx, T = MaybeRemotePlace<'tcx>, U = PcgLifetimeProjectionBase<'tcx>> {
    Place(T),
    LifetimeProjection(LifetimeProjection<'tcx, U>),
}

impl<'tcx, Ctxt, T: LabelPlaceWithContext<'tcx, Ctxt>, U: LabelPlaceWithContext<'tcx, Ctxt>>
    LabelPlaceWithContext<'tcx, Ctxt> for PcgNode<'tcx, T, U>
{
    fn label_place_with_context(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        label_context: Ctxt,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        match self {
            PcgNode::Place(p) => {
                p.label_place_with_context(predicate, labeller, label_context, ctxt)
            }
            PcgNode::LifetimeProjection(rp) => {
                rp.base
                    .label_place_with_context(predicate, labeller, label_context, ctxt)
            }
        }
    }
}

impl<'tcx> PcgNode<'tcx> {
    pub fn is_remote_place(self) -> bool {
        matches!(self, PcgNode::Place(MaybeRemotePlace::Remote(_)))
    }

    pub fn related_place(self) -> Option<MaybeRemotePlace<'tcx>> {
        match self {
            PcgNode::Place(p) => Some(p),
            PcgNode::LifetimeProjection(rp) => match rp.base() {
                PlaceOrConst::Place(p) => Some(p),
                _ => None,
            },
        }
    }

    pub fn related_maybe_labelled_place(self) -> Option<MaybeLabelledPlace<'tcx>> {
        self.related_place().and_then(|p| p.as_local_place())
    }

    pub(crate) fn related_maybe_remote_current_place(
        &self,
    ) -> Option<MaybeRemoteCurrentPlace<'tcx>> {
        match self {
            PcgNode::Place(p) => p.maybe_remote_current_place(),
            PcgNode::LifetimeProjection(rp) => rp.base().maybe_remote_current_place(),
        }
    }
}

impl<'tcx, T, U> PcgNode<'tcx, T, U> {
    pub(crate) fn is_place(&self) -> bool {
        matches!(self, PcgNode::Place(_))
    }

    pub fn expect_lifetime_projection(self) -> LifetimeProjection<'tcx, U> {
        match self {
            PcgNode::LifetimeProjection(rp) => rp,
            _ => panic!(),
        }
    }

    pub(crate) fn try_into_region_projection(self) -> Result<LifetimeProjection<'tcx, U>, Self> {
        match self {
            PcgNode::LifetimeProjection(rp) => Ok(rp),
            _ => Err(self),
        }
    }
}

impl<'tcx> From<LoopAbstractionInput<'tcx>> for PcgNode<'tcx> {
    fn from(target: LoopAbstractionInput<'tcx>) -> Self {
        target.0
    }
}

impl<'tcx, T, U: Copy + PcgLifetimeProjectionBaseLike<'tcx>> LabelLifetimeProjection<'tcx>
    for PcgNode<'tcx, T, U>
where
    PcgLifetimeProjectionBase<'tcx>: From<U>,
{
    fn label_lifetime_projection(
        &mut self,
        predicate: &LabelLifetimeProjectionPredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        repacker: CompilerCtxt<'_, 'tcx>,
    ) -> LabelLifetimeProjectionResult {
        if let PcgNode::LifetimeProjection(this_projection) = self {
            this_projection.label_lifetime_projection(predicate, label, repacker)
        } else {
            LabelLifetimeProjectionResult::Unchanged
        }
    }
}

impl<T, U> From<T> for PcgNode<'_, T, U> {
    fn from(value: T) -> Self {
        PcgNode::Place(value)
    }
}

impl<'tcx, U> From<LifetimeProjection<'tcx, U>> for PcgNode<'tcx, MaybeRemotePlace<'tcx>, U> {
    fn from(value: LifetimeProjection<'tcx, U>) -> Self {
        PcgNode::LifetimeProjection(value)
    }
}

impl<'tcx> From<LifetimeProjection<'tcx, Place<'tcx>>> for PcgNode<'tcx> {
    fn from(value: LifetimeProjection<'tcx, Place<'tcx>>) -> Self {
        PcgNode::LifetimeProjection(value.into())
    }
}

impl<'tcx> From<LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>> for PcgNode<'tcx> {
    fn from(value: LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>) -> Self {
        PcgNode::LifetimeProjection(value.into())
    }
}

impl<'tcx, T: PcgNodeLike<'tcx>, U: PcgLifetimeProjectionBaseLike<'tcx>> PcgNodeLike<'tcx>
    for PcgNode<'tcx, T, U>
{
    fn to_pcg_node<C: Copy>(self, repacker: CompilerCtxt<'_, 'tcx, C>) -> PcgNode<'tcx> {
        match self {
            PcgNode::Place(p) => p.to_pcg_node(repacker),
            PcgNode::LifetimeProjection(rp) => rp.to_pcg_node(repacker),
        }
    }
}

impl<'a, 'tcx, T: HasValidityCheck<'a, 'tcx>, U: PcgLifetimeProjectionBaseLike<'tcx>>
    HasValidityCheck<'a, 'tcx> for PcgNode<'tcx, T, U>
{
    fn check_validity(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> Result<(), String> {
        match self {
            PcgNode::Place(p) => p.check_validity(ctxt),
            PcgNode::LifetimeProjection(rp) => todo!(),
        }
    }
}

impl<
    'tcx,
    'a,
    T: PcgNodeLike<'tcx> + DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    U: PcgLifetimeProjectionBaseLike<'tcx>
        + DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
> DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>> for PcgNode<'tcx, T, U>
{
    fn to_short_string(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
        match self {
            PcgNode::Place(p) => p.to_short_string(repacker),
            PcgNode::LifetimeProjection(rp) => rp.to_short_string(repacker),
        }
    }
}

impl<
    'tcx,
    BC: Copy,
    T: PcgNodeLike<'tcx> + ToJsonWithCompilerCtxt<'tcx, BC>,
    U: PcgLifetimeProjectionBaseLike<'tcx> + ToJsonWithCompilerCtxt<'tcx, BC>,
> ToJsonWithCompilerCtxt<'tcx, BC> for PcgNode<'tcx, T, U>
{
    fn to_json(&self, _repacker: CompilerCtxt<'_, 'tcx, BC>) -> serde_json::Value {
        todo!()
    }
}

pub trait MaybeHasLocation {
    fn location(&self) -> Option<SnapshotLocation>;
}

impl<'tcx, T: MaybeHasLocation, U: PcgLifetimeProjectionBaseLike<'tcx> + MaybeHasLocation>
    MaybeHasLocation for PcgNode<'tcx, T, U>
{
    fn location(&self) -> Option<SnapshotLocation> {
        match self {
            PcgNode::Place(place) => place.location(),
            PcgNode::LifetimeProjection(region_projection) => region_projection.base().location(),
        }
    }
}

pub trait PcgNodeLike<'tcx>:
    Clone + Copy + std::fmt::Debug + Eq + PartialEq + std::hash::Hash
{
    fn to_pcg_node<C: Copy>(self, ctxt: CompilerCtxt<'_, 'tcx, C>) -> PcgNode<'tcx>;

    fn try_to_local_node<'a>(self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> Option<LocalNode<'tcx>>
    where
        'tcx: 'a,
    {
        match self.to_pcg_node(ctxt.ctxt()) {
            PcgNode::Place(p) => match p {
                MaybeRemotePlace::Local(maybe_old_place) => {
                    Some(maybe_old_place.to_local_node(ctxt.ctxt()))
                }
                MaybeRemotePlace::Remote(_) => None,
            },
            PcgNode::LifetimeProjection(rp) => match rp.base() {
                PlaceOrConst::Place(maybe_remote_place) => match maybe_remote_place {
                    MaybeRemotePlace::Local(maybe_old_place) => {
                        Some(rp.with_base(maybe_old_place).to_local_node(ctxt.ctxt()))
                    }
                    MaybeRemotePlace::Remote(_) => None,
                },
                PlaceOrConst::Const(_) => None,
            },
        }
    }
}

pub(crate) trait LocalNodeLike<'tcx> {
    fn to_local_node<C: Copy>(self, repacker: CompilerCtxt<'_, 'tcx, C>) -> LocalNode<'tcx>;
}

impl<'tcx> LocalNodeLike<'tcx> for mir::Place<'tcx> {
    fn to_local_node<C: Copy>(self, _ctxt: CompilerCtxt<'_, 'tcx, C>) -> LocalNode<'tcx> {
        LocalNode::Place(self.into())
    }
}

impl From<RemotePlace> for PcgNode<'_> {
    fn from(remote_place: RemotePlace) -> Self {
        PcgNode::Place(remote_place.into())
    }
}
