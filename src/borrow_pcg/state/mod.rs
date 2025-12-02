//! The data structure representing the state of the Borrow PCG.

use std::{borrow::Cow, marker::PhantomData};

use crate::{
    borrow_pcg::{
        borrow_pcg_edge::BlockingNode,
        edge_data::LabelEdgePlaces,
        graph::join::JoinBorrowsArgs,
        has_pcs_elem::LabelLifetimeProjection,
        validity_conditions::{EMPTY_VALIDITY_CONDITIONS_REF, JoinValidityConditionsResult},
    },
    pcg::{
        PcgNodeLike, SymbolicCapability,
        place_capabilities::{PlaceCapabilitiesReader, SymbolicPlaceCapabilities},
    },
    utils::{HasBorrowCheckerCtxt, data_structures::HashSet},
};

use super::{
    borrow_pcg_edge::{BlockedNode, BorrowPcgEdge, BorrowPcgEdgeRef, ToBorrowsEdge},
    graph::BorrowsGraph,
    validity_conditions::{PathCondition, ValidityConditions},
    visitor::extract_regions,
};
use crate::{
    action::BorrowPcgAction,
    borrow_pcg::{
        action::{BorrowPcgActionKind, LabelPlaceReason},
        edge::{
            borrow::BorrowEdge,
            kind::BorrowPcgEdgeKind,
            outlives::{BorrowFlowEdge, BorrowFlowEdgeKind},
        },
        edge_data::EdgeData,
        has_pcs_elem::{LabelLifetimeProjectionPredicate, PlaceLabeller, SetLabel},
        region_projection::{LifetimeProjection, LifetimeProjectionLabel},
    },
    error::PcgError,
    pcg::{
        CapabilityKind, PcgNode,
        ctxt::AnalysisCtxt,
        place_capabilities::{PlaceCapabilities, PlaceCapabilitiesInterface},
    },
    pcg_validity_assert,
    rustc_interface::middle::{
        mir::{self, BasicBlock, BorrowKind, Location, MutBorrowKind},
        ty::{self},
    },
    utils::{
        CompilerCtxt, Place, display::DebugLines, place::maybe_old::MaybeLabelledPlace,
        remote::RemotePlace, validity::HasValidityCheck,
    },
};

/// The state of the Borrow PCG, including the Borrow PCG graph and the validity
/// conditions associated with the current basic block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BorrowsState<
    'a,
    'tcx,
    EdgeKind: PartialEq + Eq + std::hash::Hash = BorrowPcgEdgeKind<'tcx>,
> {
    pub(crate) graph: BorrowsGraph<'tcx, EdgeKind>,
    pub(crate) validity_conditions: &'a ValidityConditions,
    _marker: PhantomData<&'tcx ()>,
}

impl<'a, 'tcx, EdgeKind: PartialEq + Eq + std::hash::Hash> Default
    for BorrowsState<'a, 'tcx, EdgeKind>
{
    fn default() -> Self {
        Self {
            graph: BorrowsGraph::default(),
            validity_conditions: EMPTY_VALIDITY_CONDITIONS_REF,
            _marker: PhantomData,
        }
    }
}

pub(crate) struct BorrowStateMutRef<'pcg, 'tcx, EdgeKind = BorrowPcgEdgeKind<'tcx>> {
    pub(crate) graph: &'pcg mut BorrowsGraph<'tcx, EdgeKind>,
    pub(crate) validity_conditions: &'pcg ValidityConditions,
}

pub(crate) struct BorrowStateRef<'pcg, 'tcx, EdgeKind = BorrowPcgEdgeKind<'tcx>> {
    pub(crate) graph: &'pcg BorrowsGraph<'tcx, EdgeKind>,
    #[allow(unused)]
    pub(crate) path_conditions: &'pcg ValidityConditions,
}

impl<'pcg, 'tcx, EdgeKind> Clone for BorrowStateRef<'pcg, 'tcx, EdgeKind> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'pcg, 'tcx, EdgeKind> Copy for BorrowStateRef<'pcg, 'tcx, EdgeKind> {}

pub(crate) trait BorrowsStateLike<'tcx, EdgeKind = BorrowPcgEdgeKind<'tcx>> {
    fn as_mut_ref(&mut self) -> BorrowStateMutRef<'_, 'tcx, EdgeKind>;
    fn as_ref(&self) -> BorrowStateRef<'_, 'tcx, EdgeKind>;

    fn graph_mut(&mut self) -> &mut BorrowsGraph<'tcx, EdgeKind> {
        self.as_mut_ref().graph
    }
    fn graph(&self) -> &BorrowsGraph<'tcx>;

    fn label_place_and_update_related_capabilities<'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>>(
        &mut self,
        place: Place<'tcx>,
        reason: LabelPlaceReason,
        labeller: &impl PlaceLabeller<'tcx>,
        capabilities: &mut impl PlaceCapabilitiesInterface<'tcx, SymbolicCapability>,
        ctxt: Ctxt,
    ) -> bool
    where
        'tcx: 'a,
        EdgeKind: LabelEdgePlaces<'tcx> + Eq + std::hash::Hash,
    {
        let state = self.as_mut_ref();
        state.graph.label_place(place, reason, labeller, ctxt);
        // If in a join we don't want to change capabilities because this will
        // essentially be handled by the join logic.
        // See 69_http_header_map.rs
        if reason != LabelPlaceReason::JoinOwnedReadAndWriteCapabilities {
            capabilities.retain(|p, _| !p.projects_indirection_from(place, ctxt));
        }
        true
    }

    fn label_region_projection<'a>(
        &mut self,
        predicate: &LabelLifetimeProjectionPredicate<'tcx>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> bool
    where
        'tcx: 'a,
        EdgeKind: LabelLifetimeProjection<'a, 'tcx> + Eq + std::hash::Hash,
    {
        self.graph_mut()
            .label_region_projection(predicate, label, ctxt)
    }

    fn remove<'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>>(
        &mut self,
        edge: &EdgeKind,
        capabilities: &mut impl PlaceCapabilitiesInterface<'tcx, SymbolicCapability>,
        ctxt: Ctxt,
    ) -> bool
    where
        'tcx: 'a,
        EdgeKind: EdgeData<'tcx> + Eq + std::hash::Hash,
    {
        let state = self.as_mut_ref();
        let removed = state.graph.remove(edge).is_some();
        if removed {
            for node in edge.blocked_by_nodes(ctxt.bc_ctxt()) {
                if !state.graph.contains(node, ctxt.bc_ctxt())
                    && let PcgNode::Place(MaybeLabelledPlace::Current(place)) = node
                {
                    let _ = capabilities.remove(place, ctxt);
                }
            }
        }
        removed
    }

    fn apply_action<'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>>(
        &mut self,
        action: BorrowPcgAction<'tcx, EdgeKind>,
        capabilities: &mut impl PlaceCapabilitiesInterface<'tcx, SymbolicCapability>,
        ctxt: Ctxt,
    ) -> Result<bool, PcgError>
    where
        'tcx: 'a,
        EdgeKind: EdgeData<'tcx>
            + LabelEdgePlaces<'tcx>
            + LabelLifetimeProjection<'a, 'tcx>
            + Eq
            + std::hash::Hash,
    {
        let result = match action.kind {
            BorrowPcgActionKind::Restore(restore) => {
                let restore_place = restore.place();
                if let Some(cap) = capabilities.get(restore_place, ctxt) {
                    pcg_validity_assert!(cap.expect_concrete() < restore.capability())
                }
                if !capabilities.insert(restore_place, restore.capability(), ctxt) {
                    // panic!("Capability should have been updated")
                }
                if restore.capability() == CapabilityKind::Exclusive {
                    self.label_region_projection(
                        &LabelLifetimeProjectionPredicate::AllFuturePostfixes(restore_place),
                        None,
                        ctxt,
                    );
                }
                true
            }
            BorrowPcgActionKind::Weaken(weaken) => {
                let weaken_place = weaken.place();
                pcg_validity_assert!(
                    capabilities
                        .get(weaken_place, ctxt)
                        .unwrap()
                        .expect_concrete()
                        == weaken.from,
                    [ctxt],
                    "Weakening from {:?} to {:?} is not valid",
                    capabilities
                        .get(weaken_place, ctxt)
                        .unwrap()
                        .expect_concrete(),
                    weaken.from
                );
                match weaken.to {
                    Some(to) => {
                        capabilities.insert(weaken_place, to, ctxt);
                    }
                    None => {
                        assert!(capabilities.remove(weaken_place, ctxt).is_some());
                    }
                }
                true
            }
            BorrowPcgActionKind::MakePlaceOld(action) => self
                .label_place_and_update_related_capabilities(
                    action.place,
                    action.reason,
                    &SetLabel(action.location),
                    capabilities,
                    ctxt,
                ),
            BorrowPcgActionKind::RemoveEdge(edge) => self.remove(&edge.value, capabilities, ctxt),
            BorrowPcgActionKind::AddEdge { edge } => self.graph_mut().insert(edge, ctxt.bc_ctxt()),
            BorrowPcgActionKind::LabelLifetimeProjection(rp, label) => {
                self.label_region_projection(&rp, label, ctxt.bc_ctxt())
            }
        };
        Ok(result)
    }
}

impl<'pcg, 'tcx: 'pcg> BorrowsStateLike<'tcx> for BorrowStateMutRef<'pcg, 'tcx> {
    fn as_mut_ref(&mut self) -> BorrowStateMutRef<'_, 'tcx> {
        BorrowStateMutRef {
            graph: self.graph,
            validity_conditions: self.validity_conditions,
        }
    }

    fn graph(&self) -> &BorrowsGraph<'tcx> {
        self.graph
    }

    fn as_ref(&self) -> BorrowStateRef<'_, 'tcx> {
        BorrowStateRef {
            graph: self.graph,
            path_conditions: self.validity_conditions,
        }
    }
}

impl<'a, 'tcx> BorrowsStateLike<'tcx> for BorrowsState<'a, 'tcx> {
    fn as_mut_ref(&mut self) -> BorrowStateMutRef<'_, 'tcx> {
        BorrowStateMutRef {
            graph: &mut self.graph,
            validity_conditions: self.validity_conditions,
        }
    }

    fn graph(&self) -> &BorrowsGraph<'tcx> {
        &self.graph
    }

    fn as_ref(&self) -> BorrowStateRef<'_, 'tcx> {
        BorrowStateRef {
            graph: &self.graph,
            path_conditions: self.validity_conditions,
        }
    }
}

impl<'pcg, 'tcx> From<&'pcg mut BorrowsState<'_, 'tcx>> for BorrowStateMutRef<'pcg, 'tcx> {
    fn from(borrows_state: &'pcg mut BorrowsState<'_, 'tcx>) -> Self {
        Self {
            graph: &mut borrows_state.graph,
            validity_conditions: borrows_state.validity_conditions,
        }
    }
}

impl<'tcx> DebugLines<CompilerCtxt<'_, 'tcx>> for BorrowsState<'_, 'tcx> {
    fn debug_lines(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Vec<Cow<'static, str>> {
        let mut lines = Vec::new();
        lines.extend(self.graph.debug_lines(ctxt));
        lines
    }
}

impl<'tcx> HasValidityCheck<'_, 'tcx> for BorrowStateRef<'_, 'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.graph.check_validity(ctxt)?;
        Ok(())
    }
}

impl<'tcx> HasValidityCheck<'_, 'tcx> for BorrowStateMutRef<'_, 'tcx> {
    fn check_validity(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Result<(), String> {
        self.as_ref().check_validity(ctxt)
    }
}

impl<'a, 'tcx> BorrowsState<'a, 'tcx> {
    fn introduce_initial_borrows(
        &mut self,
        local: mir::Local,
        capabilities: &mut PlaceCapabilities<'tcx, SymbolicCapability>,
        ctxt: AnalysisCtxt<'a, 'tcx>,
    ) {
        let local_decl = &ctxt.ctxt.body().local_decls[local];
        let arg_place: Place<'tcx> = local.into();
        for region in extract_regions(local_decl.ty) {
            let region_projection =
                LifetimeProjection::new(arg_place.into(), region, None, ctxt.ctxt).unwrap();
            assert!(
                self.apply_action(
                    BorrowPcgAction::add_edge(
                        BorrowPcgEdge::new(
                            BorrowFlowEdge::new(
                                LifetimeProjection::new(
                                    RemotePlace::new(local).into(),
                                    region,
                                    None,
                                    ctxt.ctxt,
                                )
                                .unwrap_or_else(|| {
                                    panic!(
                                        "Failed to create region for remote place (for {local:?}).
                                    Local ty: {:?} does not have region {:?}",
                                        local_decl.ty, region
                                    );
                                }),
                                region_projection,
                                BorrowFlowEdgeKind::InitialBorrows,
                                ctxt.ctxt,
                            )
                            .into(),
                            ValidityConditions::new(),
                        ),
                        "Introduce initial borrows",
                        ctxt.ctxt,
                    ),
                    capabilities,
                    ctxt,
                )
                .unwrap()
            );
        }
    }

    pub(crate) fn start_block(
        capabilities: &mut PlaceCapabilities<'tcx, SymbolicCapability>,
        analysis_ctxt: AnalysisCtxt<'a, 'tcx>,
    ) -> Self {
        let mut borrow = Self::default();
        for arg in analysis_ctxt.body().args_iter() {
            borrow.introduce_initial_borrows(arg, capabilities, analysis_ctxt);
        }
        borrow
    }

    pub fn graph(&self) -> &BorrowsGraph<'tcx> {
        &self.graph
    }

    pub(crate) fn join(
        &mut self,
        other: &Self,
        args: JoinBorrowsArgs<'_, 'a, 'tcx>,
        ctxt: AnalysisCtxt<'a, 'tcx>,
    ) -> Result<(), PcgError> {
        self.graph
            .join(&other.graph, self.validity_conditions, args, ctxt)?;
        if let JoinValidityConditionsResult::Changed(new_validity_conditions) = self
            .validity_conditions
            .join_result(other.validity_conditions, ctxt.body())
        {
            self.validity_conditions = ctxt.arena.alloc(new_validity_conditions);
        }
        Ok(())
    }

    /// Remove all edges that are not valid for `path`, based on their validity
    /// conditions.
    pub fn filter_for_path(&mut self, path: &[BasicBlock], ctxt: CompilerCtxt<'_, 'tcx>) {
        self.graph.filter_for_path(path, ctxt);
    }

    /// Returns the place that blocks `node` if:
    /// 1. there is exactly one hyperedge blocking `node`
    /// 2. that edge is blocked by exactly one node
    /// 3. that node is a region projection that can be dereferenced
    ///
    /// This is used in the symbolic-execution based purification encoding to
    /// compute the backwards function for the argument local `place`. It
    /// depends on `Borrow` edges connecting the remote input to a single node
    /// in the PCG. In the symbolic execution, backward function results are computed
    /// per-path, so this expectation may be reasonable in that context.
    pub fn get_place_blocking(
        &self,
        place: MaybeLabelledPlace<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Option<MaybeLabelledPlace<'tcx>> {
        let edges = self.edges_blocking(place.to_pcg_node(ctxt), ctxt);
        if edges.len() != 1 {
            return None;
        }
        let nodes = edges[0].blocked_by_nodes(ctxt).collect::<Vec<_>>();
        if nodes.len() != 1 {
            return None;
        }
        let node = nodes.into_iter().next().unwrap();
        match node {
            PcgNode::Place(_) => todo!(),
            PcgNode::LifetimeProjection(region_projection) => region_projection.deref(ctxt),
        }
    }

    pub(crate) fn edges_blocking<'slf, 'mir: 'slf, 'bc: 'slf>(
        &'slf self,
        node: BlockedNode<'tcx>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> Vec<BorrowPcgEdgeRef<'tcx, 'slf>> {
        self.graph.edges_blocking(node, ctxt).collect()
    }

    pub fn nodes_blocking<'slf, 'mir: 'slf, 'bc: 'slf>(
        &'slf self,
        node: BlockedNode<'tcx>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> HashSet<BlockingNode<'tcx>> {
        self.graph
            .edges_blocking(node, ctxt)
            .flat_map(|e| e.blocked_by_nodes(ctxt).collect::<Vec<_>>())
            .collect()
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn add_borrow<Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>>(
        &mut self,
        blocked_place: Place<'tcx>,
        assigned_place: Place<'tcx>,
        kind: BorrowKind,
        location: Location,
        region: ty::Region<'tcx>,
        capabilities: &mut SymbolicPlaceCapabilities<'tcx>,
        ctxt: Ctxt,
    ) where
        'tcx: 'a,
    {
        assert!(
            assigned_place.ty(ctxt).ty.ref_mutability().is_some(),
            "{:?}:{:?} Assigned place {:?} is not a reference. Ty: {:?}",
            ctxt.body().source.def_id(),
            location,
            assigned_place,
            assigned_place.ty(ctxt).ty
        );
        let borrow_edge = BorrowEdge::new(
            blocked_place.into(),
            assigned_place.into(),
            kind,
            location,
            region,
            ctxt,
        );
        assert!(self.graph.insert(
            borrow_edge.to_borrow_pcg_edge(self.validity_conditions.clone()),
            ctxt.ctxt()
        ));

        match kind {
            BorrowKind::Mut {
                kind: MutBorrowKind::Default | MutBorrowKind::ClosureCapture,
            } => {
                let _ = capabilities.remove(blocked_place, ctxt);
            }
            _ => {
                let blocked_place_capability = capabilities.get(blocked_place, ctxt);
                match blocked_place_capability.map(|c| c.expect_concrete()) {
                    Some(CapabilityKind::Exclusive) => {
                        assert!(capabilities.insert(blocked_place, CapabilityKind::Read, ctxt));
                    }
                    Some(CapabilityKind::Read) => {
                        // Do nothing, this just adds another shared borrow
                    }
                    other => {
                        // Shouldn't be None or Write, due to capability updates
                        // based on the TripleWalker analysis
                        pcg_validity_assert!(
                            false,
                            "{:?}: Unexpected capability for borrow blocked place {:?}: {:?}",
                            location,
                            blocked_place,
                            other
                        );
                    }
                }
            }
        }
    }
}

impl<'a, 'tcx, EdgeKind: PartialEq + Eq + std::hash::Hash> BorrowsState<'a, 'tcx, EdgeKind> {
    pub(crate) fn add_cfg_edge(
        &mut self,
        from: BasicBlock,
        to: BasicBlock,
        ctxt: AnalysisCtxt<'a, 'tcx>,
    ) -> bool {
        pcg_validity_assert!(
            !ctxt.ctxt.is_back_edge(from, to),
            [ctxt],
            "Adding CFG edge from {from:?} to {to:?} is a back edge"
        );
        let pc = PathCondition::new(from, to);
        let mut validity_conditions = self.validity_conditions.clone();
        validity_conditions.insert(pc, ctxt.body());
        self.validity_conditions = ctxt.arena.alloc(validity_conditions);
        self.graph.add_path_condition(pc, ctxt.ctxt)
    }
}
