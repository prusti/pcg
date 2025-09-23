//! Definitions of edges in the Borrow PCG.
use std::marker::PhantomData;

use itertools::Itertools;
use rustc_interface::middle::mir::{self, BasicBlock, PlaceElem};

use super::{
    borrow_pcg_expansion::BorrowPcgExpansion,
    edge::outlives::BorrowFlowEdge,
    edge_data::EdgeData,
    graph::Conditioned,
    has_pcs_elem::LabelLifetimeProjection,
    region_projection::{LifetimeProjection, LifetimeProjectionLabel, LocalLifetimeProjection},
    validity_conditions::ValidityConditions,
};
use crate::{
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::{
        edge::{
            abstraction::AbstractionEdge, borrow::BorrowEdge, deref::DerefEdge,
            kind::BorrowPcgEdgeKind,
        },
        edge_data::{edgedata_enum, LabelEdgePlaces, LabelPlacePredicate},
        has_pcs_elem::{
            LabelLifetimeProjectionPredicate, LabelLifetimeProjectionResult, PlaceLabeller,
        },
        region_projection::LocalLifetimeProjectionBase,
    },
    coupling::PcgCoupledEdgeKind,
    error::PcgError,
    pcg::PcgNode,
    rustc_interface,
    utils::{
        display::DisplayWithCompilerCtxt, place::{maybe_old::MaybeLabelledPlace, maybe_remote::MaybeRemotePlace}, validity::HasValidityCheck, CompilerCtxt, HasCompilerCtxt, HasPlace, Place, PlaceProjectable
    },
};

/// A reference to an edge in the Borrow PCG
#[derive(Debug, Eq, PartialEq, Hash)]
pub struct BorrowPcgEdgeRef<'tcx, 'graph, EdgeKind = BorrowPcgEdgeKind<'tcx>> {
    pub(crate) kind: &'graph EdgeKind,
    pub(crate) conditions: &'graph ValidityConditions,
    _marker: PhantomData<&'tcx ()>,
}

impl<
    'a,
    'tcx,
    'graph,
    EdgeKind: DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
> DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for BorrowPcgEdgeRef<'tcx, 'graph, EdgeKind>
{
    fn to_short_string(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
        self.conditions.conditional_string(self.kind, ctxt)
    }
}

impl<'tcx, 'graph, EdgeKind> BorrowPcgEdgeRef<'tcx, 'graph, EdgeKind> {
    pub(crate) fn new(kind: &'graph EdgeKind, conditions: &'graph ValidityConditions) -> Self {
        Self {
            kind,
            conditions,
            _marker: PhantomData,
        }
    }
}

impl<'tcx, 'graph, EdgeKind> BorrowPcgEdgeRef<'tcx, 'graph, EdgeKind> {
    pub fn kind(&self) -> &EdgeKind {
        self.kind
    }
}

impl<'tcx, 'graph, EdgeKind> Copy for BorrowPcgEdgeRef<'tcx, 'graph, EdgeKind> {}

impl<'tcx, 'graph, EdgeKind> Clone for BorrowPcgEdgeRef<'tcx, 'graph, EdgeKind> {
    fn clone(&self) -> Self {
        *self
    }
}

pub type BorrowPcgEdge<'tcx, Kind = BorrowPcgEdgeKind<'tcx>> = Conditioned<Kind>;

impl<'tcx> LabelEdgePlaces<'tcx> for BorrowPcgEdge<'tcx> {
    fn label_blocked_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.value.label_blocked_places(predicate, labeller, ctxt)
    }

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelPlacePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.value
            .label_blocked_by_places(predicate, labeller, ctxt)
    }
}

impl<'tcx> LabelLifetimeProjection<'tcx> for BorrowPcgEdge<'tcx> {
    fn label_lifetime_projection(
        &mut self,
        predicate: &LabelLifetimeProjectionPredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> LabelLifetimeProjectionResult {
        self.value.label_lifetime_projection(predicate, label, ctxt)
    }
}

/// Either a [`BorrowPcgEdge`] or a [`BorrowPcgEdgeRef`]
pub trait BorrowPcgEdgeLike<'tcx, Kind = BorrowPcgEdgeKind<'tcx>>:
    EdgeData<'tcx> + Clone + std::fmt::Debug
{
    fn kind(&self) -> &Kind;
    fn conditions(&self) -> &ValidityConditions;
    fn to_owned_edge(self) -> BorrowPcgEdge<'tcx>;

    fn blocked_places<'slf>(
        &'slf self,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> impl Iterator<Item = MaybeRemotePlace<'tcx>> + 'slf
    where
        'tcx: 'slf,
    {
        self.blocked_nodes(ctxt)
            .flat_map(|node| node.as_place())
            .unique()
    }
}

impl<'tcx> BorrowPcgEdgeLike<'tcx> for BorrowPcgEdge<'tcx> {
    fn kind(&self) -> &BorrowPcgEdgeKind<'tcx> {
        &self.value
    }

    fn conditions(&self) -> &ValidityConditions {
        &self.conditions
    }

    fn to_owned_edge(self) -> BorrowPcgEdge<'tcx> {
        self
    }
}

impl<'tcx, 'graph> BorrowPcgEdgeLike<'tcx> for BorrowPcgEdgeRef<'tcx, 'graph> {
    fn kind<'baz>(&'baz self) -> &'graph BorrowPcgEdgeKind<'tcx> {
        self.kind
    }

    fn conditions(&self) -> &ValidityConditions {
        self.conditions
    }

    fn to_owned_edge(self) -> BorrowPcgEdge<'tcx> {
        BorrowPcgEdge::new(self.kind.clone(), self.conditions.clone())
    }
}

impl<'tcx, T: BorrowPcgEdgeLike<'tcx>> HasValidityCheck<'_, 'tcx> for T {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.kind().check_validity(ctxt)
    }
}

impl<'tcx> LocalNode<'tcx> {
    pub(crate) fn is_old(&self) -> bool {
        match self {
            PcgNode::Place(p) => p.is_old(),
            PcgNode::LifetimeProjection(region_projection) => region_projection.base().is_old(),
        }
    }
    pub(crate) fn related_current_place(self) -> Option<Place<'tcx>> {
        match self {
            PcgNode::Place(p) => p.as_current_place(),
            PcgNode::LifetimeProjection(rp) => rp.base().as_current_place(),
        }
    }
}

/// Any node in the PCG that is "local" in the sense that it can be named by
/// referring to a (potentially labelled) place, i.e. any node with an associated
/// place.
/// This excludes nodes that refer to remote places or constants.
pub type LocalNode<'tcx> =
    PcgNode<'tcx, MaybeLabelledPlace<'tcx>, LocalLifetimeProjectionBase<'tcx>>;

impl<'tcx> HasPlace<'tcx> for LocalNode<'tcx> {
    fn is_place(&self) -> bool {
        match self {
            LocalNode::Place(_) => true,
            LocalNode::LifetimeProjection(_) => false,
        }
    }

    fn place(&self) -> Place<'tcx> {
        match self {
            LocalNode::Place(p) => p.place(),
            LocalNode::LifetimeProjection(rp) => rp.base().place(),
        }
    }

    fn place_mut(&mut self) -> &mut Place<'tcx> {
        match self {
            LocalNode::Place(p) => p.place_mut(),
            LocalNode::LifetimeProjection(rp) => rp.place_mut().place_mut(),
        }
    }

    fn iter_projections<C: Copy>(
        &self,
        repacker: CompilerCtxt<'_, 'tcx, C>,
    ) -> Vec<(Self, PlaceElem<'tcx>)> {
        match self {
            LocalNode::Place(p) => p
                .iter_projections(repacker)
                .into_iter()
                .map(|(p, e)| (p.into(), e))
                .collect(),
            LocalNode::LifetimeProjection(rp) => rp
                .iter_projections(repacker)
                .into_iter()
                .map(|(p, e)| (LocalNode::LifetimeProjection(p), e))
                .collect(),
        }
    }

}

impl<'tcx> PlaceProjectable<'tcx> for LocalNode<'tcx> {
    fn project_deeper<'a>(
        &self,
        elem: PlaceElem<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Result<Self, PcgError> {
        Ok(match self {
            LocalNode::Place(p) => LocalNode::Place(p.project_deeper(elem, ctxt)?),
            LocalNode::LifetimeProjection(rp) => {
                LocalNode::LifetimeProjection(rp.project_deeper(elem, ctxt)?)
            }
        })
    }
}

impl<'tcx> From<LocalLifetimeProjection<'tcx>> for LocalNode<'tcx> {
    fn from(rp: LocalLifetimeProjection<'tcx>) -> Self {
        LocalNode::LifetimeProjection(rp)
    }
}

impl<'tcx> TryFrom<LocalNode<'tcx>> for MaybeLabelledPlace<'tcx> {
    type Error = ();
    fn try_from(node: LocalNode<'tcx>) -> Result<Self, Self::Error> {
        match node {
            LocalNode::Place(maybe_old_place) => Ok(maybe_old_place),
            LocalNode::LifetimeProjection(_) => Err(()),
        }
    }
}

impl<'tcx> From<Place<'tcx>> for LocalNode<'tcx> {
    fn from(place: Place<'tcx>) -> Self {
        LocalNode::Place(place.into())
    }
}

impl<'tcx> From<LifetimeProjection<'tcx, Place<'tcx>>> for LocalNode<'tcx> {
    fn from(rp: LifetimeProjection<'tcx, Place<'tcx>>) -> Self {
        rp.with_base(MaybeLabelledPlace::Current(rp.base)).into()
    }
}

/// A node that could potentially block other nodes in the PCG, i.e. any node
/// other than a [`crate::utils::place::remote::RemotePlace`] (which are roots
/// by definition)
pub type BlockingNode<'tcx> = LocalNode<'tcx>;

impl<'tcx> HasValidityCheck<'_, 'tcx> for MaybeRemotePlace<'tcx> {
    fn check_validity(&self, _ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        Ok(())
    }
}

impl<T: std::fmt::Display> std::fmt::Display for PcgNode<'_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PcgNode::Place(p) => write!(f, "{p}"),
            PcgNode::LifetimeProjection(rp) => write!(f, "{rp}"),
        }
    }
}

impl<'tcx> LocalNode<'tcx> {
    pub fn as_current_place(self) -> Option<Place<'tcx>> {
        match self {
            LocalNode::Place(MaybeLabelledPlace::Current(place)) => Some(place),
            _ => None,
        }
    }
}

/// A node that could potentially be blocked in the PCG. In principle any kind
/// of PCG node could be blocked; however this type alias should be preferred to
/// [`PcgNode`] in contexts where the blocking is relevant.
pub type BlockedNode<'tcx> = PcgNode<'tcx>;

impl<'tcx> PcgNode<'tcx> {
    pub(crate) fn as_blocking_node<'a>(&self) -> Option<BlockingNode<'tcx>>
    where
        'tcx: 'a,
    {
        self.as_local_node()
    }

    pub(crate) fn as_local_node<'a>(&self) -> Option<LocalNode<'tcx>>
    where
        'tcx: 'a,
    {
        match self {
            PcgNode::Place(MaybeRemotePlace::Local(maybe_old_place)) => {
                Some(LocalNode::Place(*maybe_old_place))
            }
            PcgNode::Place(MaybeRemotePlace::Remote(_)) => None,
            PcgNode::LifetimeProjection(rp) => {
                let place = rp.base().as_local_place()?;
                Some(LocalNode::LifetimeProjection(rp.with_base(place)))
            }
        }
    }
    pub fn as_current_place(&self) -> Option<Place<'tcx>> {
        match self {
            BlockedNode::Place(MaybeRemotePlace::Local(MaybeLabelledPlace::Current(place))) => {
                Some(*place)
            }
            _ => None,
        }
    }

    pub(crate) fn as_place(&self) -> Option<MaybeRemotePlace<'tcx>> {
        match self {
            BlockedNode::Place(maybe_remote_place) => Some(*maybe_remote_place),
            BlockedNode::LifetimeProjection(_) => None,
        }
    }
}

impl<'tcx> From<mir::Place<'tcx>> for BlockedNode<'tcx> {
    fn from(place: mir::Place<'tcx>) -> Self {
        BlockedNode::Place(place.into())
    }
}

impl<'tcx> From<Place<'tcx>> for BlockedNode<'tcx> {
    fn from(place: Place<'tcx>) -> Self {
        BlockedNode::Place(place.into())
    }
}

impl<'tcx> From<MaybeLabelledPlace<'tcx>> for BlockedNode<'tcx> {
    fn from(maybe_old_place: MaybeLabelledPlace<'tcx>) -> Self {
        BlockedNode::Place(maybe_old_place.into())
    }
}

impl<'tcx> From<LocalNode<'tcx>> for BlockedNode<'tcx> {
    fn from(blocking_node: LocalNode<'tcx>) -> Self {
        match blocking_node {
            LocalNode::Place(maybe_old_place) => BlockedNode::Place(maybe_old_place.into()),
            LocalNode::LifetimeProjection(rp) => BlockedNode::LifetimeProjection(rp.into()),
        }
    }
}

impl<'tcx> BorrowPcgEdge<'tcx> {
    /// The conditions under which the edge is valid
    pub fn conditions(&self) -> &ValidityConditions {
        &self.conditions
    }

    /// Whether the edge is valid for a given path (depending on its associated
    /// validity conditions)
    pub fn valid_for_path(&self, path: &[BasicBlock], body: &mir::Body<'_>) -> bool {
        self.conditions.valid_for_path(path, body)
    }

    pub fn kind(&self) -> &BorrowPcgEdgeKind<'tcx> {
        &self.value
    }
}

impl<'tcx, T: BorrowPcgEdgeLike<'tcx>> EdgeData<'tcx> for T {
    fn blocked_by_nodes<'slf, 'mir: 'slf, BC: Copy + 'slf>(
        &'slf self,
        ctxt: CompilerCtxt<'mir, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = LocalNode<'tcx>> + 'slf>
    where
        'tcx: 'mir,
    {
        self.kind().blocked_by_nodes(ctxt)
    }

    fn blocked_nodes<'slf, BC: Copy>(
        &'slf self,
        repacker: CompilerCtxt<'_, 'tcx, BC>,
    ) -> Box<dyn std::iter::Iterator<Item = PcgNode<'tcx>> + 'slf>
    where
        'tcx: 'slf,
    {
        self.kind().blocked_nodes(repacker)
    }

    fn blocks_node<'slf>(&self, node: BlockedNode<'tcx>, repacker: CompilerCtxt<'_, 'tcx>) -> bool {
        self.kind().blocks_node(node, repacker)
    }

    fn is_blocked_by<'slf>(&self, node: LocalNode<'tcx>, repacker: CompilerCtxt<'_, 'tcx>) -> bool {
        self.kind().is_blocked_by(node, repacker)
    }
}

edgedata_enum!(
    BorrowPcgEdgeKind<'tcx>,
    Borrow(BorrowEdge<'tcx>),
    BorrowPcgExpansion(BorrowPcgExpansion<'tcx>),
    Abstraction(AbstractionEdge<'tcx>),
    BorrowFlow(BorrowFlowEdge<'tcx>),
    Deref(DerefEdge<'tcx>),
    Coupled(PcgCoupledEdgeKind<'tcx>),
);

impl<'tcx, 'a> DisplayWithCompilerCtxt<'tcx, &'a dyn BorrowCheckerInterface<'tcx>>
    for &BorrowPcgEdgeKind<'tcx>
{
    fn to_short_string(
        &self,
        ctxt: CompilerCtxt<'_, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>>,
    ) -> String {
        (*self).to_short_string(ctxt)
    }
}

pub(crate) trait ToBorrowsEdge<'tcx> {
    fn to_borrow_pcg_edge(self, conditions: ValidityConditions) -> BorrowPcgEdge<'tcx>;
}

impl<'tcx> ToBorrowsEdge<'tcx> for BorrowPcgExpansion<'tcx, LocalNode<'tcx>> {
    fn to_borrow_pcg_edge(self, conditions: ValidityConditions) -> BorrowPcgEdge<'tcx> {
        BorrowPcgEdge::new(BorrowPcgEdgeKind::BorrowPcgExpansion(self), conditions)
    }
}

impl<'tcx> ToBorrowsEdge<'tcx> for AbstractionEdge<'tcx> {
    fn to_borrow_pcg_edge(self, conditions: ValidityConditions) -> BorrowPcgEdge<'tcx> {
        BorrowPcgEdge::new(BorrowPcgEdgeKind::Abstraction(self), conditions)
    }
}

impl<'tcx> ToBorrowsEdge<'tcx> for BorrowEdge<'tcx> {
    fn to_borrow_pcg_edge(self, conditions: ValidityConditions) -> BorrowPcgEdge<'tcx> {
        BorrowPcgEdge::new(BorrowPcgEdgeKind::Borrow(self), conditions)
    }
}

impl<'tcx> ToBorrowsEdge<'tcx> for BorrowFlowEdge<'tcx> {
    fn to_borrow_pcg_edge(self, conditions: ValidityConditions) -> BorrowPcgEdge<'tcx> {
        BorrowPcgEdge::new(BorrowPcgEdgeKind::BorrowFlow(self), conditions)
    }
}

impl<'tcx, T: ToBorrowsEdge<'tcx>> From<Conditioned<T>> for BorrowPcgEdge<'tcx> {
    fn from(val: Conditioned<T>) -> Self {
        val.value.to_borrow_pcg_edge(val.conditions)
    }
}
