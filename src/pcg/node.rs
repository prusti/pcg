use crate::{
    borrow_pcg::{
        borrow_pcg_edge::LocalNode,
        domain::LoopAbstractionInput,
        edge_data::{LabelNodePredicate, NodeReplacement},
        graph::loop_abstraction::MaybeRemoteCurrentPlace,
        has_pcs_elem::{
            LabelLifetimeProjection, LabelLifetimeProjectionResult, LabelNodeContext, LabelPlace,
            PlaceLabeller,
        },
        region_projection::{
            HasRegions, LifetimeProjection, LifetimeProjectionLabel, OverrideRegionDebugString,
            PcgLifetimeProjectionBase, PcgLifetimeProjectionBaseLike, PlaceOrConst,
        },
    },
    rustc_interface::middle::mir,
    utils::{
        CompilerCtxt, DebugCtxt, HasCompilerCtxt, PcgPlace, Place, PrefixRelation,
        SnapshotLocation,
        data_structures::HashSet,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
        json::ToJsonWithCtxt,
        maybe_old::MaybeLabelledPlace,
        place::maybe_remote::MaybeRemotePlace,
        validity::HasValidityCheck,
    },
};

#[deprecated(note = "Use `PcgNode` instead")]
pub type PCGNode<'tcx> = PcgNode<'tcx>;

#[derive(PartialEq, Eq, Hash, Debug, Clone, Copy)]
pub enum PcgNodeType {
    Place,
    LifetimeProjection,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum PcgNode<'tcx, T = MaybeLabelledPlace<'tcx>, U = PcgLifetimeProjectionBase<'tcx>> {
    Place(T),
    LifetimeProjection(LifetimeProjection<'tcx, U>),
}

pub(crate) type PcgNodeWithPlace<'tcx, P = Place<'tcx>> =
    PcgNode<'tcx, MaybeLabelledPlace<'tcx, P>, PcgLifetimeProjectionBase<'tcx, P>>;

impl<'tcx, Ctxt, T: LabelPlace<'tcx, Ctxt>, U: LabelPlace<'tcx, Ctxt>> LabelPlace<'tcx, Ctxt>
    for PcgNode<'tcx, T, U>
{
    fn label_place(&mut self, labeller: &impl PlaceLabeller<'tcx, Ctxt>, ctxt: Ctxt) -> bool {
        match self {
            PcgNode::Place(p) => p.label_place(labeller, ctxt),
            PcgNode::LifetimeProjection(rp) => rp.base.label_place(labeller, ctxt),
        }
    }
}

impl<'tcx> PcgNode<'tcx> {
    pub(crate) fn related_maybe_remote_current_place(
        &self,
    ) -> Option<MaybeRemoteCurrentPlace<'tcx>> {
        match self {
            PcgNode::Place(p) => match p {
                MaybeLabelledPlace::Current(place) => Some(MaybeRemoteCurrentPlace::Local(*place)),
                MaybeLabelledPlace::Labelled(_) => None,
            },
            PcgNode::LifetimeProjection(rp) => rp.base().maybe_remote_current_place(),
        }
    }
}

impl<'tcx, P: Copy> PcgNode<'tcx, MaybeLabelledPlace<'tcx, P>, PcgLifetimeProjectionBase<'tcx, P>> {
    pub fn related_place(self) -> Option<MaybeRemotePlace<'tcx, P>> {
        match self {
            PcgNode::Place(p) => Some(p.into()),
            PcgNode::LifetimeProjection(rp) => match rp.base {
                PlaceOrConst::Place(p) => Some(p),
                _ => None,
            },
        }
    }

    pub fn related_maybe_labelled_place(self) -> Option<MaybeLabelledPlace<'tcx, P>> {
        self.related_place().and_then(|p| p.as_local_place())
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

    pub(crate) fn try_into_lifetime_projection(self) -> Result<LifetimeProjection<'tcx, U>, Self> {
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

impl<'tcx, T, U> LabelLifetimeProjection<'tcx> for PcgNode<'tcx, T, U>
where
    LifetimeProjection<'tcx, U>: LabelLifetimeProjection<'tcx>,
{
    fn label_lifetime_projection(
        &mut self,
        label: Option<LifetimeProjectionLabel>,
    ) -> LabelLifetimeProjectionResult {
        if let PcgNode::LifetimeProjection(this_projection) = self {
            this_projection.label_lifetime_projection(label)
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

impl<'tcx, Ctxt, P, T: PcgNodeLike<'tcx, Ctxt, P>, U: PcgLifetimeProjectionBaseLike<'tcx, P>>
    PcgNodeLike<'tcx, Ctxt, P> for PcgNode<'tcx, T, U>
{
    fn to_pcg_node(self, ctxt: Ctxt) -> PcgNodeWithPlace<'tcx, P> {
        match self {
            PcgNode::Place(p) => p.to_pcg_node(ctxt),
            PcgNode::LifetimeProjection(rp) => rp.to_pcg_node(ctxt),
        }
    }
}

impl<'tcx, Ctxt: Copy + DebugCtxt, T: HasValidityCheck<Ctxt>, U> HasValidityCheck<Ctxt>
    for PcgNode<'tcx, T, U>
where
    LifetimeProjection<'tcx, U>: HasValidityCheck<Ctxt>,
{
    fn check_validity(&self, ctxt: Ctxt) -> Result<(), String> {
        match self {
            PcgNode::Place(p) => p.check_validity(ctxt),
            PcgNode::LifetimeProjection(rp) => rp.check_validity(ctxt),
        }
    }
}

impl<'tcx, Ctxt, T: DisplayWithCtxt<Ctxt>, U> DisplayWithCtxt<Ctxt> for PcgNode<'tcx, T, U>
where
    LifetimeProjection<'tcx, U>: DisplayWithCtxt<Ctxt>,
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        match self {
            PcgNode::Place(p) => p.display_output(ctxt, mode),
            PcgNode::LifetimeProjection(rp) => rp.display_output(ctxt, mode),
        }
    }
}

impl<'tcx, T, U, Ctxt> ToJsonWithCtxt<Ctxt> for PcgNode<'tcx, T, U> {
    fn to_json(&self, _ctxt: Ctxt) -> serde_json::Value {
        todo!()
    }
}

pub trait MaybeHasLocation {
    fn location(&self) -> Option<SnapshotLocation>;
}

impl<'tcx, T: MaybeHasLocation, U: MaybeHasLocation> MaybeHasLocation for PcgNode<'tcx, T, U> {
    fn location(&self) -> Option<SnapshotLocation> {
        match self {
            PcgNode::Place(place) => place.location(),
            PcgNode::LifetimeProjection(region_projection) => region_projection.base.location(),
        }
    }
}

pub trait PcgNodeLike<'tcx, Ctxt, P>:
    Clone + Copy + std::fmt::Debug + Eq + PartialEq + std::hash::Hash
{
    fn to_pcg_node(self, ctxt: Ctxt) -> PcgNodeWithPlace<'tcx, P>;

    fn try_to_local_node<'a>(self, ctxt: Ctxt) -> Option<LocalNode<'tcx, P>> {
        match self.to_pcg_node(ctxt) {
            PcgNode::Place(p) => Some(p.into()),
            PcgNode::LifetimeProjection(rp) => match rp.base {
                PlaceOrConst::Place(maybe_remote_place) => match maybe_remote_place {
                    MaybeRemotePlace::Local(maybe_old_place) => {
                        Some(rp.with_base(maybe_old_place).to_local_node(ctxt))
                    }
                    MaybeRemotePlace::Remote(_) => None,
                },
                PlaceOrConst::Const(_) => None,
            },
        }
    }
}

macro_rules! pcg_node_like_wrapper {
    ($ty:ty) => {
        impl<'tcx, Ctxt, P: $crate::utils::PcgNodeComponent> PcgNodeLike<'tcx, Ctxt, P> for $ty
        where
            <Self as std::ops::Deref>::Target: PcgNodeLike<'tcx, Ctxt, P>,
        {
            fn to_pcg_node(self, ctxt: Ctxt) -> PcgNodeWithPlace<'tcx, P> {
                use std::ops::Deref;
                self.deref().to_pcg_node(ctxt)
            }
        }
    };
}
pub(crate) use pcg_node_like_wrapper;

pub(crate) trait LabelPlaceConditionally<'tcx, Ctxt, P: PcgPlace<'tcx, Ctxt>>:
    PcgNodeLike<'tcx, Ctxt, P> + LabelPlace<'tcx, Ctxt, P>
{
    fn label_place_conditionally(
        &mut self,
        replacements: &mut HashSet<NodeReplacement<'tcx, P>>,
        predicate: &LabelNodePredicate<'tcx, P>,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        node_context: LabelNodeContext,
        ctxt: Ctxt,
    ) {
        let orig = self.to_pcg_node(ctxt);
        if predicate.applies_to(orig, node_context) {
            let changed = self.label_place(labeller, ctxt);
            if changed {
                replacements.insert(NodeReplacement::new(orig, self.to_pcg_node(ctxt)));
            }
        }
    }
}

impl<'tcx, Ctxt, P: PcgPlace<'tcx, Ctxt>, T: PcgNodeLike<'tcx, Ctxt, P> + LabelPlace<'tcx, Ctxt, P>>
    LabelPlaceConditionally<'tcx, Ctxt, P> for T
{
}

pub(crate) trait LocalNodeLike<'tcx, Ctxt, P = Place<'tcx>>:
    Copy + PcgNodeLike<'tcx, Ctxt, P>
{
    fn to_local_node(self, ctxt: Ctxt) -> LocalNode<'tcx, P>;
}

impl<'tcx, Ctxt> LocalNodeLike<'tcx, Ctxt> for mir::Place<'tcx> {
    fn to_local_node(self, _ctxt: Ctxt) -> LocalNode<'tcx> {
        LocalNode::Place(self.into())
    }
}

impl<'tcx, Ctxt> PcgNodeLike<'tcx, Ctxt, Place<'tcx>> for mir::Place<'tcx> {
    fn to_pcg_node(self, _ctxt: Ctxt) -> PcgNode<'tcx> {
        self.into()
    }
}
