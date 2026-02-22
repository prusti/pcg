//! Defines the Borrow PCG Graph
pub(crate) mod aliases;
pub(crate) mod frozen;
pub(crate) mod join;
pub(crate) mod loop_abstraction;
pub(crate) mod materialize;
mod mutate;

use std::{borrow::Cow, marker::PhantomData};

use crate::{
    borrow_pcg::{
        borrow_pcg_expansion::{BorrowPcgExpansion, BorrowPcgPlaceExpansion, ExpansionMutability},
        edge_data::{LabelEdgeLifetimeProjections, LabelNodePredicate},
        has_pcs_elem::LabelLifetimeProjectionResult,
        region_projection::LifetimeProjectionLabel,
        validity_conditions::ValidityConditionOps,
    },
    coupling::PcgCoupledEdgeKind,
    error::PcgUnsupportedError,
    owned_pcg::ExpandedPlace,
    pcg::{PcgNode, PcgNodeLike, PcgNodeWithPlace},
    rustc_interface::{
        ast::Mutability,
        data_structures::fx::FxHashSet,
        middle::mir::{self},
    },
    utils::{
        CompilerCtxt, DebugCtxt, DebugImgcat, HasBorrowCheckerCtxt, HasCompilerCtxt,
        PcgNodeComponent, PcgPlace, PcgSettings, Place, PlaceLike,
        data_structures::{HashMap, HashSet},
        display::{
            DebugLines, DisplayOutput, DisplayWithCompilerCtxt, DisplayWithCtxt, OutputMode,
        },
        maybe_old::MaybeLabelledPlace,
        validity::HasValidityCheck,
    },
};
use frozen::{CachedLeafEdges, FrozenGraphRef};
use itertools::Itertools;

use super::{
    borrow_pcg_edge::{BlockedNode, BorrowPcgEdge, BorrowPcgEdgeLike, BorrowPcgEdgeRef, LocalNode},
    edge::borrow::BorrowEdge,
    edge_data::EdgeData,
    validity_conditions::ValidityConditions,
};
use crate::borrow_pcg::edge::{abstraction::AbstractionEdge, kind::BorrowPcgEdgeKind};

use crate::coupling::{MaybeCoupledEdgeKind, MaybeCoupledEdges, PcgCoupledEdges};

/// The Borrow PCG Graph.
#[derive(Clone, Debug)]
pub struct BorrowsGraph<'tcx, EdgeKind = BorrowPcgEdgeKind<'tcx>, VC = ValidityConditions> {
    pub(crate) edges: HashMap<EdgeKind, VC>,
    _marker: PhantomData<&'tcx ()>,
}

impl<EdgeKind, VC> Default for BorrowsGraph<'_, EdgeKind, VC> {
    fn default() -> Self {
        Self {
            edges: HashMap::default(),
            _marker: PhantomData,
        }
    }
}

impl<'tcx> DebugLines<CompilerCtxt<'_, 'tcx>> for BorrowsGraph<'tcx> {
    fn debug_lines(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Vec<Cow<'static, str>> {
        self.edges()
            .map(|edge| edge.test_string(ctxt))
            .sorted()
            .collect()
    }
}

impl<'a, 'tcx: 'a, Ctxt: Copy + DebugCtxt + HasBorrowCheckerCtxt<'a, 'tcx>> HasValidityCheck<Ctxt>
    for BorrowsGraph<'tcx>
where
    BorrowPcgEdgeKind<'tcx>: EdgeData<'tcx, Ctxt, Place<'tcx>> + DisplayWithCtxt<Ctxt>,
{
    fn check_validity(&self, ctxt: Ctxt) -> Result<(), String> {
        let nodes = self.nodes(ctxt);
        for node in &nodes {
            if let Some(PcgNode::LifetimeProjection(rp)) = node.try_to_local_node(ctxt)
                && rp.is_future()
                && rp.base.as_current_place().is_some()
            {
                let current_rp = rp.with_label(None, ctxt);
                let conflicting_edges =
                    self.edges_blocking(PcgNode::LifetimeProjection(current_rp.rebase()), ctxt)
                        .chain(self.edges_blocked_by(
                            PcgNode::LifetimeProjection(current_rp.rebase()),
                            ctxt,
                        ))
                        .collect::<HashSet<_>>();
                if !conflicting_edges.is_empty() {
                    return Err(format!(
                        "Placeholder region projection {} has edges blocking or blocked by its current version {}:\n\t{}",
                        rp.display_string(ctxt),
                        current_rp.display_string(ctxt),
                        conflicting_edges
                            .iter()
                            .map(|e| e.display_string(ctxt))
                            .join("\n\t")
                    ));
                }
            }
        }
        for edge in self.edges() {
            if let BorrowPcgEdgeKind::BorrowPcgExpansion(e) = edge.kind()
                && let Some(place) = e.base().as_current_place()
                && place.projects_shared_ref(ctxt)
            {
                edge.check_validity(ctxt.bc_ctxt())?;
            }
        }
        Ok(())
    }
}

impl<Kind: Eq + std::hash::Hash + PartialEq, VC: Eq> Eq for BorrowsGraph<'_, Kind, VC> {}

impl<Kind: Eq + std::hash::Hash + PartialEq, VC: PartialEq> PartialEq
    for BorrowsGraph<'_, Kind, VC>
{
    fn eq(&self, other: &Self) -> bool {
        self.edges == other.edges
    }
}

pub(crate) fn borrows_imgcat_debug(
    block: mir::BasicBlock,
    debug_imgcat: Option<DebugImgcat>,
    settings: &PcgSettings,
) -> bool {
    if let Some(debug_block) = settings.debug_block
        && debug_block != block
    {
        return false;
    }
    if let Some(debug_imgcat) = debug_imgcat {
        settings.debug_imgcat.contains(&debug_imgcat)
    } else {
        !settings.debug_imgcat.is_empty()
    }
}

impl<'tcx, EdgeKind, VC> BorrowsGraph<'tcx, EdgeKind, VC> {
    pub(crate) fn descendant_edges<'slf, Ctxt: Copy + DebugCtxt, P: PcgPlace<'tcx, Ctxt>>(
        &'slf self,
        node: BlockedNode<'tcx, P>,
        ctxt: Ctxt,
    ) -> HashSet<BorrowPcgEdgeRef<'tcx, 'slf, EdgeKind, VC>>
    where
        EdgeKind: EdgeData<'tcx, Ctxt, P> + Eq + std::hash::Hash,
        VC: Eq + std::hash::Hash,
    {
        let mut seen: HashSet<BlockedNode<'tcx, P>> = HashSet::default();
        let mut result: HashSet<BorrowPcgEdgeRef<'tcx, 'slf, EdgeKind, VC>> = HashSet::default();
        let mut stack = vec![node];
        while let Some(node) = stack.pop() {
            if seen.insert(node) {
                for edge in self.edges_blocking(node, ctxt) {
                    result.insert(edge);
                    for node in edge.kind.blocked_by_nodes(ctxt) {
                        stack.push(node.into());
                    }
                }
            }
        }
        result
    }

    pub(crate) fn nodes<Ctxt: Copy + DebugCtxt, P: PcgPlace<'tcx, Ctxt>>(
        &self,
        ctxt: Ctxt,
    ) -> FxHashSet<PcgNodeWithPlace<'tcx, P>>
    where
        EdgeKind: std::hash::Hash + Eq + EdgeData<'tcx, Ctxt, P>,
    {
        self.edges()
            .flat_map(|edge| {
                edge.kind
                    .blocked_nodes(ctxt)
                    .chain(
                        edge.kind
                            .blocked_by_nodes(ctxt)
                            .map(std::convert::Into::into),
                    )
                    .collect::<Vec<_>>()
            })
            .collect()
    }

    pub(crate) fn edges_blocking<'slf, Ctxt: Copy + DebugCtxt, P: PcgNodeComponent>(
        &'slf self,
        node: BlockedNode<'tcx, P>,
        ctxt: Ctxt,
    ) -> impl Iterator<Item = BorrowPcgEdgeRef<'tcx, 'slf, EdgeKind, VC>>
    where
        EdgeKind: EdgeData<'tcx, Ctxt, P> + std::hash::Hash + Eq,
    {
        self.edges()
            .filter(move |edge| edge.kind.blocks_node(node, ctxt))
    }
}

impl<'tcx, P: PcgNodeComponent, VC> BorrowsGraph<'tcx, BorrowPcgEdgeKind<'tcx, P>, VC> {
    pub(crate) fn abstraction_edge_kinds<'slf>(
        &'slf self,
    ) -> impl Iterator<Item = &'slf AbstractionEdge<'tcx, P>> + 'slf {
        self.edges().filter_map(|edge| match edge.kind {
            BorrowPcgEdgeKind::Abstraction(abstraction) => Some(abstraction),
            _ => None,
        })
    }

    /// Returns true iff `edge` connects two nodes within an abstraction edge
    fn is_encapsulated_by_abstraction<Ctxt: Copy + DebugCtxt, Edge: EdgeData<'tcx, Ctxt, P>>(
        &self,
        edge: &Edge,
        ctxt: Ctxt,
    ) -> bool
    where
        P: PcgPlace<'tcx, Ctxt>,
        BorrowPcgEdgeKind<'tcx, P>: EdgeData<'tcx, Ctxt, P>,
        AbstractionEdge<'tcx, P>: EdgeData<'tcx, Ctxt, P>,
    {
        'outer: for abstraction in self.abstraction_edge_kinds() {
            for blocked in edge.blocked_nodes(ctxt) {
                if !abstraction.blocks_node(blocked, ctxt) {
                    continue 'outer;
                }
            }
            for blocked_by in edge.blocked_by_nodes(ctxt) {
                if !abstraction.is_blocked_by(blocked_by, ctxt) {
                    continue 'outer;
                }
            }
            return true;
        }
        false
    }

    pub(crate) fn places<Ctxt: Copy + DebugCtxt>(&self, ctxt: Ctxt) -> HashSet<P>
    where
        BorrowPcgEdgeKind<'tcx, P>: EdgeData<'tcx, Ctxt, P>,
        P: PcgPlace<'tcx, Ctxt>,
    {
        self.nodes(ctxt)
            .into_iter()
            .filter_map(|node| match node {
                PcgNode::Place(place) => place.as_current_place(),
                _ => None,
            })
            .collect()
    }

    pub(crate) fn contains_borrow_pcg_expansion<Ctxt: Copy + DebugCtxt>(
        &self,
        expanded_place: &ExpandedPlace<'tcx, P>,
        ctxt: Ctxt,
    ) -> Result<bool, PcgUnsupportedError<'tcx>>
    where
        P: PlaceLike<'tcx, Ctxt>,
        BorrowPcgEdgeKind<'tcx, P>: EdgeData<'tcx, Ctxt, P>,
    {
        let expanded_places = expanded_place.expansion_places(ctxt)?;
        let nodes = self.nodes(ctxt);
        Ok(expanded_places
            .into_iter()
            .all(|place| nodes.contains(&place.to_pcg_node(ctxt))))
    }

    pub fn edges_blocked_by<'graph, Ctxt: Copy + DebugCtxt>(
        &'graph self,
        node: LocalNode<'tcx, P>,
        ctxt: Ctxt,
    ) -> impl Iterator<Item = BorrowPcgEdgeRef<'tcx, 'graph, BorrowPcgEdgeKind<'tcx, P>, VC>>
    where
        BorrowPcgEdgeKind<'tcx, P>: EdgeData<'tcx, Ctxt, P>,
    {
        self.edges()
            .filter(move |edge| edge.kind.blocked_by_nodes(ctxt).contains(&node))
    }
}

pub(crate) enum BorrowedCapability {
    Exclusive,
    Read,
    None,
}

impl<'tcx> BorrowsGraph<'tcx> {
    pub(crate) fn is_transitively_blocked<'a, Ctxt: DebugCtxt + HasCompilerCtxt<'a, 'tcx>>(
        &self,
        place: Place<'tcx>,
        ctxt: Ctxt,
    ) -> Option<Mutability>
    where
        'tcx: 'a,
    {
        let mut result = None;
        for edge in self.descendant_edges(place.into(), ctxt) {
            match edge.kind {
                BorrowPcgEdgeKind::Borrow(borrow) => {
                    if borrow.effective_mutability().is_mut() {
                        return Some(Mutability::Mut);
                    } else {
                        result = Some(Mutability::Not);
                    }
                }
                BorrowPcgEdgeKind::Abstraction(_) => {
                    for blocked in edge.blocked_by_nodes(ctxt) {
                        match blocked {
                            PcgNode::Place(_) => todo!(),
                            PcgNode::LifetimeProjection(lifetime_projection) => {
                                if lifetime_projection.could_contain_mutable_borrows(ctxt) {
                                    return Some(Mutability::Mut);
                                } else {
                                    result = Some(Mutability::Not);
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        result
    }

    pub(crate) fn capability<'a>(
        &self,
        place: Place<'tcx>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx> + DebugCtxt,
    ) -> Option<BorrowedCapability>
    where
        'tcx: 'a,
    {
        if !self.contains(place, ctxt) {
            return None;
        }
        if place.projects_shared_ref(ctxt) {
            return Some(BorrowedCapability::Read);
        }
        match self.is_transitively_blocked(place, ctxt) {
            Some(Mutability::Mut) => return Some(BorrowedCapability::None),
            Some(Mutability::Not) => return Some(BorrowedCapability::Read),
            None => {}
        }
        if self.edges_blocking(place.into(), ctxt).next().is_some() {
            return Some(BorrowedCapability::Read);
        }
        let blocked_by_edges = self.edges_blocked_by(place.into(), ctxt);
        for edge in blocked_by_edges {
            if let BorrowPcgEdgeKind::BorrowPcgExpansion(BorrowPcgExpansion::Place(
                place_expansion,
            )) = edge.kind
            {
                if place_expansion
                    .expansion
                    .iter()
                    .all(|place| self.is_transitively_blocked(place.place(), ctxt).is_none())
                {
                    return Some(BorrowedCapability::Read);
                }
            }
        }
        Some(BorrowedCapability::Exclusive)
    }
    #[must_use]
    pub fn coupled_edges(&self) -> HashSet<Conditioned<PcgCoupledEdgeKind<'tcx>>> {
        self.edges
            .iter()
            .filter_map(|(kind, conditions)| match kind {
                BorrowPcgEdgeKind::Coupled(coupled) => {
                    Some(Conditioned::new(coupled.clone(), conditions.clone()))
                }
                _ => None,
            })
            .collect()
    }
    #[must_use]
    pub fn into_coupled(
        mut self,
    ) -> BorrowsGraph<'tcx, MaybeCoupledEdgeKind<'tcx, BorrowPcgEdgeKind<'tcx>>> {
        let coupled = PcgCoupledEdges::extract_from_data_source(&mut self);
        let mut edges: HashMap<
            MaybeCoupledEdgeKind<'tcx, BorrowPcgEdgeKind<'tcx>>,
            ValidityConditions,
        > = self
            .edges
            .into_iter()
            .map(|(kind, conditions)| (MaybeCoupledEdgeKind::NotCoupled(kind), conditions))
            .collect();
        edges.extend(
            coupled
                .into_maybe_coupled_edges()
                .into_iter()
                .flat_map(|edge| match edge {
                    MaybeCoupledEdges::Coupled(coupled) => coupled
                        .edges()
                        .into_iter()
                        .map(|edge| {
                            (
                                MaybeCoupledEdgeKind::Coupled(edge),
                                coupled.conditions().clone(),
                            )
                        })
                        .collect::<Vec<_>>(),
                    MaybeCoupledEdges::NotCoupled(not_coupled) => not_coupled
                        .into_iter()
                        .map(|edge| {
                            let borrow_pcg_edge: BorrowPcgEdge<'tcx> =
                                edge.map(BorrowPcgEdgeKind::Abstraction);
                            (
                                MaybeCoupledEdgeKind::NotCoupled(borrow_pcg_edge.value),
                                borrow_pcg_edge.conditions,
                            )
                        })
                        .collect::<Vec<_>>(),
                }),
        );
        BorrowsGraph {
            edges,
            _marker: PhantomData,
        }
    }

    pub(crate) fn leaf_places<'a>(
        &self,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> HashSet<Place<'tcx>>
    where
        'tcx: 'a,
    {
        self.frozen_graph()
            .leaf_nodes(ctxt.bc_ctxt())
            .into_iter()
            .filter_map(|node| match node {
                PcgNode::Place(place) => place.as_current_place(),
                _ => None,
            })
            .collect()
    }

    pub(crate) fn contains_deref_edge_to(&self, place: Place<'tcx>) -> bool {
        self.edges().any(|edge| {
            if let BorrowPcgEdgeKind::Deref(e) = edge.kind {
                e.deref_place == place.into()
            } else {
                false
            }
        })
    }

    pub(crate) fn owned_places(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> HashSet<Place<'tcx>> {
        let mut result = HashSet::default();
        for edge in self.edges() {
            match edge.kind {
                BorrowPcgEdgeKind::Deref(e) => {
                    if let Some(base) = e.blocked_place.as_current_place()
                        && base.is_owned(ctxt)
                    {
                        result.insert(base);
                    }
                }
                BorrowPcgEdgeKind::Borrow(borrow) => {
                    if let MaybeLabelledPlace::Current(place) = borrow.blocked_place
                        && place.is_owned(ctxt)
                    {
                        result.insert(place);
                    }
                }
                _ => {}
            }
        }
        result
    }

    pub(crate) fn take_borrow_created_at(
        &mut self,
        location: mir::Location,
    ) -> Option<Conditioned<BorrowEdge<'tcx>>> {
        self.edges
            .extract_if(|edge, _| {
                if let BorrowPcgEdgeKind::Borrow(borrow) = edge {
                    borrow.reserve_location() == location
                } else {
                    false
                }
            })
            .map(|(edge, conditions)| {
                let BorrowPcgEdgeKind::Borrow(borrow) = edge else {
                    unreachable!();
                };
                Conditioned::new(borrow, conditions)
            })
            .next()
    }

    pub(crate) fn into_edges(self) -> impl Iterator<Item = BorrowPcgEdge<'tcx>> {
        self.edges
            .into_iter()
            .map(|(kind, conditions)| BorrowPcgEdge::new(kind, conditions))
    }

    pub(crate) fn abstraction_edges<'slf>(
        &'slf self,
    ) -> impl Iterator<Item = Conditioned<&'slf AbstractionEdge<'tcx>>> + 'slf {
        self.edges().filter_map(|edge| match edge.kind {
            BorrowPcgEdgeKind::Abstraction(abstraction) => Some(Conditioned {
                conditions: edge.conditions().clone(),
                value: abstraction,
            }),
            _ => None,
        })
    }

    /// All edges that are not blocked by any other edge. The argument
    /// `blocking_map` can be provided to use a shared cache for computation
    /// of blocking calculations. The argument should be used if this function
    /// is to be called multiple times on the same graph.
    pub(crate) fn is_leaf_edge<'a: 'graph, 'graph, Edge, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>>(
        edge: &Edge,
        ctxt: Ctxt,
        blocking_map: &FrozenGraphRef<'graph, 'tcx>,
    ) -> bool
    where
        Edge: EdgeData<'tcx, Ctxt>,
        'tcx: 'a,
    {
        for n in edge.blocked_by_nodes(ctxt) {
            if blocking_map.has_edge_blocking(n.into(), ctxt) {
                return false;
            }
        }
        true
    }

    pub(crate) fn leaf_edges_set<'slf, 'a: 'slf, 'bc: 'slf>(
        &'slf self,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
        frozen_graph: &FrozenGraphRef<'slf, 'tcx>,
    ) -> CachedLeafEdges<'slf, 'tcx>
    where
        'tcx: 'a,
    {
        self.edges()
            .filter(move |edge| Self::is_leaf_edge(edge, ctxt.bc_ctxt(), frozen_graph))
            .collect()
    }

    pub(crate) fn roots(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> FxHashSet<PcgNode<'tcx>> {
        let roots: FxHashSet<PcgNode<'tcx>> = self
            .nodes(ctxt)
            .into_iter()
            .filter(|node| self.is_root(*node, ctxt))
            .collect();
        roots
    }

    pub(crate) fn is_root<T: Copy + Into<PcgNode<'tcx>>>(
        &self,
        node: T,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.contains(node.into(), ctxt)
            && match node.into().as_local_node() {
                Some(node) => match node {
                    PcgNode::Place(place) if place.place().is_owned(ctxt) => true,
                    _ => !self.has_edge_blocked_by(node, ctxt),
                },
                None => true,
            }
    }

    pub(crate) fn has_edge_blocked_by(
        &self,
        node: LocalNode<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> bool {
        self.edges().any(|edge| edge.is_blocked_by(node, ctxt))
    }

    pub(crate) fn nodes_blocked_by<'graph, 'mir: 'graph, 'bc: 'graph>(
        &'graph self,
        node: LocalNode<'tcx>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> Vec<PcgNode<'tcx>> {
        self.edges_blocked_by(node, ctxt)
            .flat_map(|edge| edge.blocked_nodes(ctxt).collect::<Vec<_>>())
            .collect()
    }

    pub(crate) fn edges_blocking_set<'slf, 'a: 'slf, 'bc: 'slf>(
        &'slf self,
        node: BlockedNode<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> Vec<BorrowPcgEdgeRef<'tcx, 'slf>>
    where
        'tcx: 'a,
    {
        self.edges_blocking(node, ctxt.bc_ctxt()).collect()
    }
}

impl<'tcx, EdgeKind: Eq + std::hash::Hash, VC> BorrowsGraph<'tcx, EdgeKind, VC> {
    pub(crate) fn remove(&mut self, edge: &EdgeKind) -> Option<VC> {
        self.edges.remove(edge)
    }

    pub fn edges<'slf>(
        &'slf self,
    ) -> impl Iterator<Item = BorrowPcgEdgeRef<'tcx, 'slf, EdgeKind, VC>> + 'slf {
        self.edges
            .iter()
            .map(|(kind, conditions)| BorrowPcgEdgeRef::new(kind, conditions))
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "type-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "type-export", ts(concrete(Conditions=String)))]
pub struct Conditioned<T, Conditions = ValidityConditions> {
    pub(crate) conditions: Conditions,
    pub(crate) value: T,
}

impl<'a, 'tcx: 'a, Ctxt: HasCompilerCtxt<'a, 'tcx>, T: DisplayWithCtxt<Ctxt>> DisplayWithCtxt<Ctxt>
    for Conditioned<T>
{
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        let output = self.value.display_output(ctxt, mode);
        match mode {
            OutputMode::Normal | OutputMode::Test => {
                self.conditions.conditional_string(output, ctxt)
            }
            OutputMode::Short => self.value.display_output(ctxt, mode),
        }
    }
}

impl<T, VC> Conditioned<T, VC> {
    pub(crate) fn new(value: T, conditions: VC) -> Self {
        Self { conditions, value }
    }

    pub fn value(&self) -> &T {
        &self.value
    }

    pub(crate) fn map<U>(self, f: impl FnOnce(T) -> U) -> Conditioned<U, VC> {
        Conditioned {
            value: f(self.value),
            conditions: self.conditions,
        }
    }
}

impl<'tcx, EdgeKind: Eq + std::hash::Hash, VC> BorrowsGraph<'tcx, EdgeKind, VC> {
    pub(crate) fn label_lifetime_projections<P, Ctxt: Copy>(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: Ctxt,
    ) -> bool
    where
        EdgeKind: LabelEdgeLifetimeProjections<'tcx, Ctxt, P>,
    {
        let mut result = false;
        self.filter_mut_edges(|edge| {
            let changed: LabelLifetimeProjectionResult = edge
                .value
                .label_lifetime_projections(predicate, label, ctxt);
            result |= changed != LabelLifetimeProjectionResult::Unchanged;
            changed.to_filter_mut_result()
        });
        result
    }
}
impl<'tcx, EdgeKind: Eq + std::hash::Hash, VC> BorrowsGraph<'tcx, EdgeKind, VC> {
    pub(crate) fn insert<'a, Ctxt: Copy>(
        &mut self,
        edge: BorrowPcgEdge<'tcx, EdgeKind, VC>,
        ctxt: Ctxt,
    ) -> bool
    where
        'tcx: 'a,
        VC: ValidityConditionOps<Ctxt>,
    {
        if let Some(conditions) = self.edges.get_mut(&edge.value) {
            conditions.join(&edge.conditions, ctxt)
        } else {
            self.edges.insert(edge.value, edge.conditions);
            true
        }
    }

    pub(crate) fn contains<
        'a,
        P: Copy + PartialEq,
        T: Into<PcgNodeWithPlace<'tcx, P>>,
        Ctxt: Copy,
    >(
        &self,
        node: T,
        ctxt: Ctxt,
    ) -> bool
    where
        'tcx: 'a,
        EdgeKind: EdgeData<'tcx, Ctxt, P>,
    {
        let node = node.into();
        self.edges().any(|edge| {
            edge.kind.blocks_node(node, ctxt)
                || node
                    .as_local_node()
                    .is_some_and(|blocking| edge.kind.blocked_by_nodes(ctxt).contains(&blocking))
        })
    }

    #[must_use]
    pub fn frozen_graph(&self) -> FrozenGraphRef<'_, 'tcx, Place<'tcx>, EdgeKind, VC> {
        FrozenGraphRef::new(self)
    }
}
