use rustc_interface::{
    ast::Mutability,
    data_structures::fx::FxHashSet,
    middle::mir::{self, BasicBlock},
};

use crate::{
    rustc_interface,
    utils::{Place, PlaceRepacker},
};

use super::{
    borrow_edge::BorrowEdge,
    borrows_graph::Conditioned,
    deref_expansion::{DerefExpansion, OwnedExpansion},
    domain::{MaybeOldPlace, MaybeRemotePlace},
    has_pcs_elem::HasPcsElems,
    path_condition::{PathCondition, PathConditions},
    region_abstraction::AbstractionEdge,
    region_projection::RegionProjection,
    region_projection_member::RegionProjectionMember,
};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct BorrowPCGEdge<'tcx> {
    conditions: PathConditions,
    pub(crate) kind: BorrowPCGEdgeKind<'tcx>,
}

/// Any node in the PCG that is "local" in the sense that it can be named
/// (include nodes that potentially refer to a past program point), i.e. any
/// node other than a [`super::domain::RemotePlace`]
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum LocalNode<'tcx> {
    Place(MaybeOldPlace<'tcx>),
    RegionProjection(RegionProjection<'tcx>),
}

/// A node that could potentially block other nodes in the PCG, i.e. any node
/// other than a [`super::domain::RemotePlace`] (which are roots by definition)
pub type BlockingNode<'tcx> = LocalNode<'tcx>;

impl<'tcx> LocalNode<'tcx> {
    pub fn is_old(&self) -> bool {
        match self {
            LocalNode::Place(maybe_old_place) => maybe_old_place.is_old(),
            LocalNode::RegionProjection(rp) => rp.place.is_old(),
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum PCGNode<'tcx> {
    Place(MaybeRemotePlace<'tcx>),
    RegionProjection(RegionProjection<'tcx>),
}

pub type BlockedNode<'tcx> = PCGNode<'tcx>;

impl<'tcx> PCGNode<'tcx> {
    pub fn as_blocking_node(&self) -> Option<BlockingNode<'tcx>> {
        self.as_local_node()
    }
    pub fn as_local_node(&self) -> Option<LocalNode<'tcx>> {
        match self {
            PCGNode::Place(MaybeRemotePlace::Local(maybe_old_place)) => {
                Some(LocalNode::Place(*maybe_old_place))
            }
            PCGNode::Place(MaybeRemotePlace::Remote(_)) => None,
            PCGNode::RegionProjection(rp) => Some(LocalNode::RegionProjection(*rp)),
        }
    }
    pub fn as_current_place(&self) -> Option<Place<'tcx>> {
        match self {
            BlockedNode::Place(MaybeRemotePlace::Local(MaybeOldPlace::Current { place })) => {
                Some(*place)
            }
            _ => None,
        }
    }
    pub fn is_old(&self) -> bool {
        match self {
            BlockedNode::Place(remote_place) => remote_place.is_old(),
            BlockedNode::RegionProjection(rp) => rp.place.is_old(),
        }
    }

    pub fn as_place(&self) -> Option<MaybeRemotePlace<'tcx>> {
        match self {
            BlockedNode::Place(maybe_remote_place) => Some(*maybe_remote_place),
            BlockedNode::RegionProjection(_) => None,
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

impl<'tcx> From<RegionProjection<'tcx>> for BlockedNode<'tcx> {
    fn from(rp: RegionProjection<'tcx>) -> Self {
        BlockedNode::RegionProjection(rp)
    }
}

impl<'tcx> From<MaybeOldPlace<'tcx>> for LocalNode<'tcx> {
    fn from(maybe_old_place: MaybeOldPlace<'tcx>) -> Self {
        LocalNode::Place(maybe_old_place)
    }
}

impl<'tcx> From<MaybeRemotePlace<'tcx>> for BlockedNode<'tcx> {
    fn from(remote_place: MaybeRemotePlace<'tcx>) -> Self {
        BlockedNode::Place(remote_place)
    }
}

impl<'tcx> From<MaybeOldPlace<'tcx>> for BlockedNode<'tcx> {
    fn from(maybe_old_place: MaybeOldPlace<'tcx>) -> Self {
        BlockedNode::Place(maybe_old_place.into())
    }
}

impl<'tcx> From<LocalNode<'tcx>> for BlockedNode<'tcx> {
    fn from(blocking_node: LocalNode<'tcx>) -> Self {
        match blocking_node {
            LocalNode::Place(maybe_old_place) => BlockedNode::Place(maybe_old_place.into()),
            LocalNode::RegionProjection(rp) => BlockedNode::RegionProjection(rp),
        }
    }
}

impl<'tcx> BorrowPCGEdge<'tcx> {
    /// true iff any of the blocked places can be mutated via the blocking places
    pub fn is_shared_borrow(&self) -> bool {
        self.kind.is_shared_borrow()
    }

    pub fn insert_path_condition(&mut self, pc: PathCondition) -> bool {
        self.conditions.insert(pc)
    }

    pub fn conditions(&self) -> &PathConditions {
        &self.conditions
    }
    pub fn valid_for_path(&self, path: &[BasicBlock]) -> bool {
        self.conditions.valid_for_path(path)
    }

    pub fn kind(&self) -> &BorrowPCGEdgeKind<'tcx> {
        &self.kind
    }

    pub fn mut_kind(&mut self) -> &mut BorrowPCGEdgeKind<'tcx> {
        &mut self.kind
    }

    pub fn new(kind: BorrowPCGEdgeKind<'tcx>, conditions: PathConditions) -> Self {
        Self { conditions, kind }
    }

    pub fn blocked_places(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<MaybeRemotePlace<'tcx>> {
        self.blocked_nodes(repacker)
            .into_iter()
            .flat_map(|node| node.as_place())
            .collect()
    }

    pub fn blocks_node(&self, node: BlockedNode<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        self.blocked_nodes(repacker).contains(&node)
    }

    pub fn blocks_region_projection(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
        rp: RegionProjection<'tcx>,
    ) -> bool {
        self.kind.blocks_region_projection(repacker, rp)
    }

    pub fn blocked_by_nodes(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<LocalNode<'tcx>> {
        self.kind.blocked_by_nodes(repacker)
    }

    fn blocked_nodes(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<BlockedNode<'tcx>> {
        self.kind.blocked_nodes(repacker)
    }
}

impl<'tcx, T> HasPcsElems<T> for BorrowPCGEdge<'tcx>
where
    BorrowPCGEdgeKind<'tcx>: HasPcsElems<T>,
{
    fn pcs_elems(&mut self) -> Vec<&mut T> {
        self.kind.pcs_elems()
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum BorrowPCGEdgeKind<'tcx> {
    Borrow(BorrowEdge<'tcx>),
    DerefExpansion(DerefExpansion<'tcx>),
    Abstraction(AbstractionEdge<'tcx>),
    RegionProjectionMember(RegionProjectionMember<'tcx>),
}

impl<'tcx> From<OwnedExpansion<'tcx>> for BorrowPCGEdgeKind<'tcx> {
    fn from(owned_expansion: OwnedExpansion<'tcx>) -> Self {
        BorrowPCGEdgeKind::DerefExpansion(DerefExpansion::OwnedExpansion(owned_expansion))
    }
}

impl<'tcx> HasPcsElems<RegionProjection<'tcx>> for BorrowPCGEdgeKind<'tcx> {
    fn pcs_elems(&mut self) -> Vec<&mut RegionProjection<'tcx>> {
        match self {
            BorrowPCGEdgeKind::RegionProjectionMember(member) => member.pcs_elems(),
            _ => vec![],
        }
    }
}

impl<'tcx, T> HasPcsElems<T> for BorrowPCGEdgeKind<'tcx>
where
    BorrowEdge<'tcx>: HasPcsElems<T>,
    RegionProjectionMember<'tcx>: HasPcsElems<T>,
    DerefExpansion<'tcx>: HasPcsElems<T>,
    AbstractionEdge<'tcx>: HasPcsElems<T>,
{
    fn pcs_elems(&mut self) -> Vec<&mut T> {
        match self {
            BorrowPCGEdgeKind::RegionProjectionMember(member) => member.pcs_elems(),
            BorrowPCGEdgeKind::Borrow(reborrow) => reborrow.pcs_elems(),
            BorrowPCGEdgeKind::DerefExpansion(deref_expansion) => deref_expansion.pcs_elems(),
            BorrowPCGEdgeKind::Abstraction(abstraction_edge) => abstraction_edge.pcs_elems(),
        }
    }
}

impl<'tcx> BorrowPCGEdgeKind<'tcx> {
    pub fn is_shared_borrow(&self) -> bool {
        match self {
            BorrowPCGEdgeKind::Borrow(reborrow) => !reborrow.is_mut(),
            _ => false,
        }
    }

    pub fn blocked_nodes(&self, repacker: PlaceRepacker<'_, 'tcx>) -> FxHashSet<BlockedNode<'tcx>> {
        match self {
            BorrowPCGEdgeKind::Borrow(de) => de.blocked_nodes(),
            BorrowPCGEdgeKind::DerefExpansion(de) => de.blocked_nodes(repacker),
            BorrowPCGEdgeKind::Abstraction(node) => node.blocked_nodes(),
            BorrowPCGEdgeKind::RegionProjectionMember(member) => member.blocked_nodes(),
        }
    }

    pub fn blocked_by_nodes(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashSet<LocalNode<'tcx>> {
        match self {
            BorrowPCGEdgeKind::Borrow(reborrow) => {
                // TODO: Region could be erased and we can't handle that yet
                if let Some(rp) = reborrow.assigned_region_projection(repacker) {
                    return vec![LocalNode::RegionProjection(rp)].into_iter().collect();
                } else {
                    FxHashSet::default()
                }
            }
            BorrowPCGEdgeKind::Abstraction(node) => node
                .outputs()
                .into_iter()
                .map(|p| LocalNode::RegionProjection(p))
                .collect(),
            BorrowPCGEdgeKind::RegionProjectionMember(member) => member.blocked_by_nodes(),
            BorrowPCGEdgeKind::DerefExpansion(de) => de.blocked_by_nodes(repacker),
        }
    }

    /// Returns true iff this edge directly blocks the given region projection
    pub fn blocks_region_projection(
        &self,
        repacker: PlaceRepacker<'_, 'tcx>,
        rp: RegionProjection<'tcx>,
    ) -> bool {
        match &self {
            BorrowPCGEdgeKind::Borrow(reborrow) => {
                reborrow.assigned_region_projection(repacker) == Some(rp)
            }
            BorrowPCGEdgeKind::DerefExpansion(deref_expansion) => {
                for place in deref_expansion.expansion(repacker) {
                    if place.region_projections(repacker).contains(&rp) {
                        return true;
                    }
                }
                false
            }
            BorrowPCGEdgeKind::Abstraction(abstraction_edge) => {
                abstraction_edge.inputs().contains(&rp)
            }
            BorrowPCGEdgeKind::RegionProjectionMember(_) => todo!(),
        }
    }
}
pub trait ToBorrowsEdge<'tcx> {
    fn to_borrow_pcg_edge(self, conditions: PathConditions) -> BorrowPCGEdge<'tcx>;
}

impl<'tcx> ToBorrowsEdge<'tcx> for DerefExpansion<'tcx> {
    fn to_borrow_pcg_edge(self, conditions: PathConditions) -> BorrowPCGEdge<'tcx> {
        BorrowPCGEdge {
            conditions,
            kind: BorrowPCGEdgeKind::DerefExpansion(self),
        }
    }
}

impl<'tcx> ToBorrowsEdge<'tcx> for AbstractionEdge<'tcx> {
    fn to_borrow_pcg_edge(self, conditions: PathConditions) -> BorrowPCGEdge<'tcx> {
        BorrowPCGEdge {
            conditions,
            kind: BorrowPCGEdgeKind::Abstraction(self),
        }
    }
}

impl<'tcx> ToBorrowsEdge<'tcx> for BorrowEdge<'tcx> {
    fn to_borrow_pcg_edge(self, conditions: PathConditions) -> BorrowPCGEdge<'tcx> {
        BorrowPCGEdge {
            conditions,
            kind: BorrowPCGEdgeKind::Borrow(self),
        }
    }
}

impl<'tcx> ToBorrowsEdge<'tcx> for RegionProjectionMember<'tcx> {
    fn to_borrow_pcg_edge(self, conditions: PathConditions) -> BorrowPCGEdge<'tcx> {
        BorrowPCGEdge {
            conditions,
            kind: BorrowPCGEdgeKind::RegionProjectionMember(self),
        }
    }
}

impl<'tcx, T: ToBorrowsEdge<'tcx>> Into<BorrowPCGEdge<'tcx>> for Conditioned<T> {
    fn into(self) -> BorrowPCGEdge<'tcx> {
        self.value.to_borrow_pcg_edge(self.conditions)
    }
}
