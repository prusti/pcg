//! Definitions of edges in the Borrow PCG.
use std::marker::PhantomData;

use crate::{
    borrow_pcg::{
        borrow_pcg_expansion::BorrowPcgExpansion, region_projection::PcgLifetimeProjectionBase,
    },
    pcg::{PcgNodeLike, PcgNodeWithPlace},
    rustc_interface::middle::mir::{self, BasicBlock, PlaceElem},
    utils::DebugCtxt,
};
use derive_more::{Deref, DerefMut};
use itertools::Itertools;

use super::{
    edge::borrow_flow::BorrowFlowEdge,
    edge_data::EdgeData,
    graph::Conditioned,
    region_projection::{LifetimeProjection, LifetimeProjectionLabel, LocalLifetimeProjection},
    validity_conditions::ValidityConditions,
};
use crate::{
    borrow_pcg::{
        edge::{
            abstraction::AbstractionEdge, borrow::BorrowEdge, deref::DerefEdge,
            kind::BorrowPcgEdgeKind,
        },
        edge_data::{
            LabelEdgeLifetimeProjections, LabelEdgePlaces, LabelNodePredicate, edgedata_enum,
        },
        has_pcs_elem::{LabelLifetimeProjectionResult, PlaceLabeller},
        region_projection::LocalLifetimeProjectionBase,
    },
    coupling::PcgCoupledEdgeKind,
    error::PcgError,
    pcg::PcgNode,
    utils::{
        CompilerCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, HasPlace, Place, PlaceProjectable,
        display::{DisplayOutput, DisplayWithCtxt, OutputMode},
        place::{maybe_old::MaybeLabelledPlace, maybe_remote::MaybeRemotePlace},
        validity::HasValidityCheck,
    },
};

/// A reference to an edge in the Borrow PCG
#[derive(Debug, Eq, PartialEq, Hash)]
pub struct BorrowPcgEdgeRef<
    'tcx,
    'graph,
    EdgeKind = BorrowPcgEdgeKind<'tcx>,
    VC = ValidityConditions,
> {
    pub(crate) kind: &'graph EdgeKind,
    pub(crate) conditions: &'graph VC,
    _marker: PhantomData<&'tcx ()>,
}

impl<'a, 'tcx: 'a, 'graph, Ctxt: HasCompilerCtxt<'a, 'tcx>, EdgeKind: DisplayWithCtxt<Ctxt>>
    DisplayWithCtxt<Ctxt> for BorrowPcgEdgeRef<'tcx, 'graph, EdgeKind>
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        let kind = self.kind.display_output(ctxt, mode);
        self.conditions.conditional_string(kind, ctxt)
    }
}

impl<'tcx, 'graph, EdgeKind, VC> BorrowPcgEdgeRef<'tcx, 'graph, EdgeKind, VC> {
    pub(crate) fn new(kind: &'graph EdgeKind, conditions: &'graph VC) -> Self {
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

pub type BorrowPcgEdge<'tcx, EdgeKind = BorrowPcgEdgeKind<'tcx>, VC = ValidityConditions> =
    Conditioned<EdgeKind, VC>;

impl<'tcx, Ctxt: DebugCtxt + Copy> LabelEdgePlaces<'tcx, Ctxt> for BorrowPcgEdge<'tcx> {
    fn label_blocked_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx, Ctxt>,
        ctxt: Ctxt,
    ) -> crate::utils::data_structures::HashSet<crate::borrow_pcg::edge_data::NodeReplacement<'tcx>>
    {
        self.value.label_blocked_places(predicate, labeller, ctxt)
    }

    fn label_blocked_by_places(
        &mut self,
        predicate: &LabelNodePredicate<'tcx>,
        labeller: &impl PlaceLabeller<'tcx, Ctxt>,
        ctxt: Ctxt,
    ) -> crate::utils::data_structures::HashSet<crate::borrow_pcg::edge_data::NodeReplacement<'tcx>>
    {
        self.value
            .label_blocked_by_places(predicate, labeller, ctxt)
    }
}

impl<'tcx, P, Ctxt, EdgeKind: LabelEdgeLifetimeProjections<'tcx, Ctxt, P>>
    LabelEdgeLifetimeProjections<'tcx, Ctxt, P> for BorrowPcgEdge<'tcx, EdgeKind>
{
    fn label_lifetime_projections(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: Ctxt,
    ) -> LabelLifetimeProjectionResult {
        self.value
            .label_lifetime_projections(predicate, label, ctxt)
    }
}

/// Either a [`BorrowPcgEdge`] or a [`BorrowPcgEdgeRef`]
pub(crate) trait BorrowPcgEdgeLike<
    'tcx,
    P: Copy + PartialEq + Eq + std::hash::Hash + 'tcx = Place<'tcx>,
    Kind = BorrowPcgEdgeKind<'tcx, P>,
>: Clone + std::fmt::Debug
{
    fn kind(&self) -> &Kind;
    fn conditions(&self) -> &ValidityConditions;
    fn to_owned_edge(self) -> BorrowPcgEdge<'tcx, Kind>;

    fn blocked_places<'slf, Ctxt: Copy>(
        &'slf self,
        ctxt: Ctxt,
    ) -> impl Iterator<Item = MaybeLabelledPlace<'tcx, P>> + 'slf
    where
        'tcx: 'slf,
        Self: EdgeData<'tcx, Ctxt, P>,
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

impl<'a, 'tcx, T: BorrowPcgEdgeLike<'tcx>> HasValidityCheck<CompilerCtxt<'a, 'tcx>> for T {
    fn check_validity(&self, ctxt: CompilerCtxt<'a, 'tcx>) -> Result<(), String> {
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
pub type LocalNode<'tcx, P = Place<'tcx>> =
    PcgNode<'tcx, MaybeLabelledPlace<'tcx, P>, LocalLifetimeProjectionBase<'tcx, P>>;

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
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>> PlaceProjectable<'tcx, Ctxt>
    for LocalNode<'tcx>
{
    fn project_deeper(&self, elem: PlaceElem<'tcx>, ctxt: Ctxt) -> Result<Self, PcgError> {
        Ok(match self {
            LocalNode::Place(p) => LocalNode::Place(p.project_deeper(elem, ctxt)?),
            LocalNode::LifetimeProjection(rp) => {
                LocalNode::LifetimeProjection(rp.project_deeper(elem, ctxt)?)
            }
        })
    }

    fn iter_projections(&self, ctxt: Ctxt) -> Vec<(Self, PlaceElem<'tcx>)> {
        match self {
            LocalNode::Place(p) => p
                .iter_projections(ctxt)
                .into_iter()
                .map(|(p, e)| (p.into(), e))
                .collect(),
            LocalNode::LifetimeProjection(rp) => rp
                .iter_projections(ctxt)
                .into_iter()
                .map(|(p, e)| (LocalNode::LifetimeProjection(p), e))
                .collect(),
        }
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

impl<'a, 'tcx> HasValidityCheck<CompilerCtxt<'a, 'tcx>> for MaybeRemotePlace<'tcx> {
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
pub type BlockedNode<'tcx, P = Place<'tcx>> =
    PcgNode<'tcx, MaybeLabelledPlace<'tcx, P>, PcgLifetimeProjectionBase<'tcx, P>>;

impl<'tcx, P: Copy> PcgNodeWithPlace<'tcx, P> {
    pub(crate) fn as_local_node<'a>(&self) -> Option<LocalNode<'tcx, P>>
    where
        'tcx: 'a,
    {
        match self {
            PcgNode::Place(place) => Some(LocalNode::Place(*place)),
            PcgNode::LifetimeProjection(rp) => {
                let place = rp.base.as_local_place()?;
                Some(LocalNode::LifetimeProjection(rp.with_base(place)))
            }
        }
    }

    pub fn as_current_place(&self) -> Option<P> {
        match self {
            BlockedNode::Place(MaybeLabelledPlace::Current(place)) => Some(*place),
            _ => None,
        }
    }
}

impl<'tcx, T: Copy, U> PcgNode<'tcx, T, U> {
    pub(crate) fn as_place(&self) -> Option<T> {
        match self {
            PcgNode::Place(p) => Some(*p),
            PcgNode::LifetimeProjection(_) => None,
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

impl<'tcx, P> From<LocalNode<'tcx, P>>
    for PcgNode<'tcx, MaybeLabelledPlace<'tcx, P>, PcgLifetimeProjectionBase<'tcx, P>>
{
    fn from(blocking_node: LocalNode<'tcx, P>) -> Self {
        match blocking_node {
            LocalNode::Place(maybe_old_place) => BlockedNode::Place(maybe_old_place),
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
edgedata_enum!(
    BorrowPcgEdgeKind<'tcx, P>,
    Borrow(BorrowEdge<'tcx, P>),
    BorrowPcgExpansion(BorrowPcgExpansion<'tcx, P>),
    Abstraction(AbstractionEdge<'tcx, P>),
    BorrowFlow(BorrowFlowEdge<'tcx, P>),
    Deref(DerefEdge<'tcx>),
    Coupled(PcgCoupledEdgeKind<'tcx>),
);

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> DisplayWithCtxt<Ctxt>
    for &BorrowPcgEdgeKind<'tcx>
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        (*self).display_output(ctxt, mode)
    }
}

pub(crate) trait ToBorrowsEdge<'tcx> {
    fn to_borrow_pcg_edge(self, conditions: ValidityConditions) -> BorrowPcgEdge<'tcx>;
}

impl<'tcx> ToBorrowsEdge<'tcx> for BorrowPcgExpansion<'tcx> {
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
