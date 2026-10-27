//! The data structure representing the state of the Borrow PCG.

use std::borrow::Cow;

use crate::{
    HasSettings,
    borrow_pcg::{
        action::ApplyActionResult,
        borrow_pcg_edge::BlockingNode,
        edge_data::{LabelEdgeLifetimeProjections, LabelEdgePlaces, display_node_replacements},
        graph::join::JoinBorrowsArgs,
        region_projection::PcgLifetimeProjectionBase,
        validity_conditions::{
            JoinValidityConditionsResult, ValidityConditionOps, ValidityConditionsLike,
        },
    },
    pcg::PcgNodeWithPlace,
    utils::{
        DebugCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, HasLocals, PlaceLike,
        data_structures::HashSet,
        display::{DisplayWithCtxt, OutputMode},
        maybe_remote::MaybeRemotePlace,
    },
};

use super::{
    borrow_pcg_edge::{BlockedNode, BorrowPcgEdge, BorrowPcgEdgeRef},
    graph::BorrowsGraph,
    validity_conditions::{PathCondition, ValidityConditions},
};
use crate::{
    action::{BorrowPcgAction, CapabilityChanges},
    borrow_pcg::{
        action::{BorrowPcgActionKind, LabelPlaceReason},
        edge::{
            borrow_flow::{BorrowFlowEdge, BorrowFlowEdgeKind},
            kind::BorrowPcgEdgeKind,
        },
        edge_data::{EdgeData, LabelNodePredicate},
        has_pcs_elem::{PlaceLabeller, SetLabel},
        region_projection::{LifetimeProjection, LifetimeProjectionLabel},
    },
    pcg::{
        CapabilityKind, PcgNode,
        ctxt::AnalysisCtxt,
        place_capabilities::{PlaceCapabilitiesInterface, PlaceCapabilitiesReader},
    },
    pcg_validity_assert,
    rustc_interface::middle::{
        mir::{self, BasicBlock},
        ty,
    },
    utils::{
        CompilerCtxt, Place, display::DebugLines, place::maybe_old::MaybeLabelledPlace,
        remote::RemotePlace, validity::HasValidityCheck,
    },
};

fn map_label_predicate<'tcx, P: Copy>(
    predicate: &LabelNodePredicate<'tcx, P>,
) -> LabelNodePredicate<'tcx, P> {
    match predicate {
        LabelNodePredicate::LifetimeProjectionLabelEquals(label) => {
            LabelNodePredicate::LifetimeProjectionLabelEquals(*label)
        }
        LabelNodePredicate::PlaceLabelEquals(location) => {
            LabelNodePredicate::PlaceLabelEquals(*location)
        }
        LabelNodePredicate::ProjectionRegionIdxEquals(region_idx) => {
            LabelNodePredicate::ProjectionRegionIdxEquals(*region_idx)
        }
        LabelNodePredicate::Equals(node) => LabelNodePredicate::Equals(*node),
        LabelNodePredicate::PlaceEquals(place) => LabelNodePredicate::PlaceEquals(*place),
        LabelNodePredicate::PlaceIsPostfixOf(place) => LabelNodePredicate::PlaceIsPostfixOf(*place),
        LabelNodePredicate::NodeType(node_type) => LabelNodePredicate::NodeType(*node_type),
        LabelNodePredicate::And(predicates) => {
            LabelNodePredicate::And(predicates.iter().map(map_label_predicate).collect())
        }
        LabelNodePredicate::Or(predicates) => {
            LabelNodePredicate::Or(predicates.iter().map(map_label_predicate).collect())
        }
        LabelNodePredicate::Not(predicate) => {
            LabelNodePredicate::Not(Box::new(map_label_predicate(predicate)))
        }
        LabelNodePredicate::EdgeType(edge_type) => LabelNodePredicate::EdgeType(*edge_type),
        LabelNodePredicate::InSourceNodes => LabelNodePredicate::InSourceNodes,
        LabelNodePredicate::InTargetNodes => LabelNodePredicate::InTargetNodes,
    }
}

/// The capability changes of ending the freeze of `place` while `refrozen`
/// stay frozen: the read unpacking of `place` becomes an exclusive one,
/// except for `refrozen` and their unpackings.
fn end_freeze<'tcx, Ctxt: Copy, P: PlaceLike<'tcx, Ctxt>>(
    place: P,
    refrozen: &[P],
    capabilities: &impl PlaceCapabilitiesReader<'tcx, CapabilityKind, P>,
    ctxt: Ctxt,
) -> CapabilityChanges<P> {
    let holders = std::iter::once(place)
        .chain(
            capabilities
                .capabilities_for_strict_postfixes_of(place)
                .map(|(p, _)| p),
        )
        .collect::<Vec<_>>();
    let mut changes = CapabilityChanges::default();
    for &p in &holders {
        if refrozen.iter().any(|t| t.is_prefix_of(p)) {
            continue;
        }
        let unpacked = holders.iter().any(|h| p.is_strict_prefix_of(*h));
        changes.set(p, exclusively_unpacked_capability(p, unpacked, ctxt));
    }
    changes
}

/// The capability changes of labelling the current value of `place`: the
/// current places that were part of the labelled value lose their
/// capabilities.
pub(crate) fn label_place_changes<'tcx, Ctxt: Copy, P: PlaceLike<'tcx, Ctxt>>(
    place: P,
    reason: LabelPlaceReason,
    capabilities: &impl PlaceCapabilitiesReader<'tcx, CapabilityKind, P>,
    ctxt: Ctxt,
) -> CapabilityChanges<P> {
    let labelled = |p: P| match reason {
        LabelPlaceReason::Detach => place.is_prefix_of(p),
        _ => p.projects_indirection_from(place, ctxt),
    };
    capabilities
        .iter()
        .filter(|(p, _)| labelled(*p))
        .map(|(p, _)| (p, None))
        .collect::<Vec<_>>()
        .into()
}

/// The capability of `place` in an exclusive unpacking: an `unpacked` place
/// keeps none (`e` for a mutable reference, R for a dereferenced shared
/// reference), and a leaf has E. Places behind a shared reference keep R.
fn exclusively_unpacked_capability<'tcx, Ctxt: Copy, P: PlaceLike<'tcx, Ctxt>>(
    place: P,
    unpacked: bool,
    ctxt: Ctxt,
) -> Option<CapabilityKind> {
    let behind_shared_ref = place
        .iter_projections(ctxt)
        .into_iter()
        .any(|(base, elem)| {
            matches!(elem, mir::ProjectionElem::Deref)
                && matches!(
                    base.rust_ty(ctxt).kind(),
                    ty::Ref(_, _, ty::Mutability::Not)
                )
        });
    if behind_shared_ref {
        return Some(CapabilityKind::Read);
    }
    if !unpacked {
        return Some(CapabilityKind::Exclusive);
    }
    match place.rust_ty(ctxt).kind() {
        ty::Ref(_, _, ty::Mutability::Mut) => Some(CapabilityKind::ShallowExclusive),
        ty::Ref(_, _, ty::Mutability::Not) => Some(CapabilityKind::Read),
        _ => None,
    }
}

/// The state of the Borrow PCG, including the Borrow PCG graph and the validity
/// conditions associated with the current basic block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BorrowsState<
    'a,
    'tcx,
    EdgeKind: PartialEq + Eq + std::hash::Hash = BorrowPcgEdgeKind<'tcx>,
    VC = ValidityConditions,
> {
    pub(crate) graph: BorrowsGraph<'tcx, EdgeKind, VC>,
    pub(crate) validity_conditions: &'a VC,
}

impl<EdgeKind: PartialEq + Eq + std::hash::Hash, VC: ValidityConditionsLike> Default
    for BorrowsState<'_, '_, EdgeKind, VC>
{
    fn default() -> Self {
        Self {
            graph: BorrowsGraph::default(),
            validity_conditions: VC::EMPTY,
        }
    }
}

pub(crate) struct BorrowStateMutRef<
    'pcg,
    'tcx,
    EdgeKind = BorrowPcgEdgeKind<'tcx>,
    VC = ValidityConditions,
> {
    pub(crate) graph: &'pcg mut BorrowsGraph<'tcx, EdgeKind, VC>,
    pub(crate) validity_conditions: &'pcg VC,
}

impl<'pcg, 'tcx, EdgeKind, VC> BorrowStateMutRef<'pcg, 'tcx, EdgeKind, VC> {
    pub(crate) fn new(
        graph: &'pcg mut BorrowsGraph<'tcx, EdgeKind, VC>,
        validity_conditions: &'pcg VC,
    ) -> Self {
        Self {
            graph,
            validity_conditions,
        }
    }
}

pub(crate) struct BorrowStateRef<
    'pcg,
    'tcx,
    EdgeKind = BorrowPcgEdgeKind<'tcx>,
    VC = ValidityConditions,
> {
    pub(crate) graph: &'pcg BorrowsGraph<'tcx, EdgeKind, VC>,
    #[allow(unused)]
    pub(crate) validity_conditions: &'pcg VC,
}

impl<'pcg, 'tcx, EdgeKind: std::hash::Hash + Eq, VC> BorrowStateRef<'pcg, 'tcx, EdgeKind, VC> {
    pub(crate) fn new(
        graph: &'pcg BorrowsGraph<'tcx, EdgeKind, VC>,
        validity_conditions: &'pcg VC,
    ) -> Self {
        Self {
            graph,
            validity_conditions,
        }
    }
}

impl<EdgeKind, VC> Clone for BorrowStateRef<'_, '_, EdgeKind, VC> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<EdgeKind, VC> Copy for BorrowStateRef<'_, '_, EdgeKind, VC> {}

pub(crate) trait BorrowsStateLike<'tcx, EdgeKind = BorrowPcgEdgeKind<'tcx>, VC = ValidityConditions>
{
    fn as_mut_ref(&mut self) -> BorrowStateMutRef<'_, 'tcx, EdgeKind, VC>;
    fn as_ref(&self) -> BorrowStateRef<'_, 'tcx, EdgeKind, VC>;

    fn graph_mut(&mut self) -> &mut BorrowsGraph<'tcx, EdgeKind, VC> {
        self.as_mut_ref().graph
    }
    fn graph(&self) -> &BorrowsGraph<'tcx, EdgeKind, VC>;

    /// Labels the current value of `place` in the graph; the capability
    /// changes are those of [`label_place_changes`].
    fn label_place<
        'a,
        P: PlaceLike<'tcx, Ctxt> + DisplayWithCtxt<Ctxt>,
        Ctxt: Copy + HasCompilerCtxt<'a, 'tcx>,
    >(
        &mut self,
        place: P,
        reason: LabelPlaceReason,
        labeller: &impl PlaceLabeller<'tcx, Ctxt, P>,
        ctxt: Ctxt,
    ) -> ApplyActionResult
    where
        'tcx: 'a,
        EdgeKind: LabelEdgePlaces<'tcx, Ctxt, P> + Eq + std::hash::Hash,
        VC: ValidityConditionOps<Ctxt>,
        PcgNodeWithPlace<'tcx, P>: DisplayWithCtxt<Ctxt>,
    {
        let state = self.as_mut_ref();
        let replacements = state.graph.label_place(place, reason, labeller, ctxt);
        let display = display_node_replacements(&replacements, ctxt, OutputMode::Normal);
        ApplyActionResult {
            changed: true,
            change_summary: display,
        }
    }

    fn label_lifetime_projections<'a, P, Ctxt: Copy>(
        &mut self,
        predicate: &LabelNodePredicate<'tcx, P>,
        label: Option<LifetimeProjectionLabel>,
        ctxt: Ctxt,
    ) -> bool
    where
        'tcx: 'a,
        EdgeKind: LabelEdgeLifetimeProjections<'tcx, Ctxt, P> + Eq + std::hash::Hash,
        VC: ValidityConditionOps<Ctxt>,
    {
        self.graph_mut()
            .label_lifetime_projections(predicate, label, ctxt)
    }

    fn apply_action<
        'a,
        Ctxt: DebugCtxt + HasCompilerCtxt<'a, 'tcx> + HasSettings<'a>,
        P: PlaceLike<'tcx, Ctxt> + DisplayWithCtxt<Ctxt>,
    >(
        &mut self,
        action: &mut BorrowPcgAction<'tcx, EdgeKind, P, VC>,
        capabilities: &mut impl PlaceCapabilitiesInterface<'tcx, CapabilityKind, P>,
        ctxt: Ctxt,
    ) -> ApplyActionResult
    where
        'tcx: 'a,
        VC: ValidityConditionOps<Ctxt> + Clone,
        EdgeKind: EdgeData<'tcx, Ctxt, P>
            + LabelEdgePlaces<'tcx, Ctxt, P>
            + LabelEdgeLifetimeProjections<'tcx, Ctxt, P>
            + Eq
            + std::hash::Hash
            + Clone,
        MaybeRemotePlace<'tcx, P>: DisplayWithCtxt<Ctxt>,
    {
        // The changes the kind determines, then the ones given with the action.
        let mut changes = CapabilityChanges::default();
        let mut result = ApplyActionResult::changed_no_display();
        match &action.kind {
            BorrowPcgActionKind::Weaken(weaken) => {
                let current = capabilities.get(weaken.place, ctxt);
                pcg_validity_assert!(
                    current == Some(weaken.from) && weaken.from > weaken.to,
                    [ctxt],
                    "Weakening {} with capability {:?} from {:?} to {:?}",
                    weaken.place.display_string(ctxt),
                    current,
                    weaken.from,
                    weaken.to
                );
                changes.set(weaken.place, Some(weaken.to));
            }
            BorrowPcgActionKind::Freeze { place } => {
                pcg_validity_assert!(
                    matches!(
                        capabilities.get(*place, ctxt),
                        Some(CapabilityKind::Exclusive | CapabilityKind::ShallowExclusive) | None
                    ),
                    [ctxt],
                    "Freezing {} with capability {:?}",
                    place.display_string(ctxt),
                    capabilities.get(*place, ctxt)
                );
                changes.set(*place, Some(CapabilityKind::Read));
                for (p, cap) in capabilities.capabilities_for_strict_postfixes_of(*place) {
                    pcg_validity_assert!(
                        !cap.is_write(),
                        [ctxt],
                        "Freezing {} with uninitialised {}",
                        place.display_string(ctxt),
                        p.display_string(ctxt)
                    );
                    changes.set(p, Some(CapabilityKind::Read));
                }
            }
            BorrowPcgActionKind::Unfreeze { place, refrozen } => {
                pcg_validity_assert!(
                    capabilities.get(*place, ctxt) == Some(CapabilityKind::Read),
                    [ctxt],
                    "Unfreezing {} with capability {:?}",
                    place.display_string(ctxt),
                    capabilities.get(*place, ctxt)
                );
                changes = end_freeze(*place, refrozen, capabilities, ctxt);
            }
            BorrowPcgActionKind::ActivateTwoPhaseBorrow { borrow } => {
                let place = borrow.blocked_place.place();
                pcg_validity_assert!(
                    capabilities.get(place, ctxt) == Some(CapabilityKind::Read),
                    [ctxt],
                    "Activating a two-phase borrow of {} with capability {:?}",
                    place.display_string(ctxt),
                    capabilities.get(place, ctxt)
                );
                changes.set(place, None);
            }
            BorrowPcgActionKind::LabelPlace(label) => {
                changes = label_place_changes(label.place, label.reason, capabilities, ctxt);
                result =
                    self.label_place(label.place, label.reason, &SetLabel(label.location), ctxt);
            }
            BorrowPcgActionKind::RemoveEdge { edge } => {
                let graph = self.graph_mut();
                let removed = graph.remove(&edge.value).is_some();
                for node in edge.value.blocked_by_nodes(ctxt) {
                    if !graph.contains(node, ctxt)
                        && let PcgNode::Place(MaybeLabelledPlace::Current(place)) = node
                        && capabilities.get(place, ctxt).is_some()
                    {
                        changes.set(place, None);
                    }
                }
                for (place, cap) in action.capabilities.iter() {
                    if let (Some(current), Some(cap)) = (capabilities.get(place, ctxt), cap) {
                        pcg_validity_assert!(current < cap, [ctxt]);
                    }
                }
                result = ApplyActionResult::from_changed(removed);
            }
            BorrowPcgActionKind::AddEdge { edge } => {
                result =
                    ApplyActionResult::from_changed(self.graph_mut().insert(edge.clone(), ctxt));
            }
            BorrowPcgActionKind::Lend { place, edge } => {
                self.graph_mut().insert(edge.clone(), ctxt);
                changes.set(*place, None);
            }
            BorrowPcgActionKind::LabelLifetimeProjection(label) => {
                let predicate = map_label_predicate(label.predicate());
                result = ApplyActionResult::from_changed(self.label_lifetime_projections(
                    &predicate,
                    label.label(),
                    ctxt,
                ));
            }
        }
        changes.extend(&action.capabilities);
        result.changed |= if matches!(
            action.kind,
            BorrowPcgActionKind::Unfreeze { .. } | BorrowPcgActionKind::RemoveEdge { .. }
        ) {
            self.regain(&changes, capabilities, ctxt)
        } else {
            changes.apply(capabilities, ctxt)
        };
        action.capabilities = changes;
        result
    }

    /// Gives back the capabilities `changes`; the places that get E back are
    /// accessed exclusively again.
    fn regain<'a, Ctxt: Copy, P: Copy + Eq + std::hash::Hash>(
        &mut self,
        changes: &CapabilityChanges<P>,
        capabilities: &mut impl PlaceCapabilitiesInterface<'tcx, CapabilityKind, P>,
        ctxt: Ctxt,
    ) -> bool
    where
        'tcx: 'a,
        EdgeKind: LabelEdgeLifetimeProjections<'tcx, Ctxt, P> + Eq + std::hash::Hash,
        VC: ValidityConditionOps<Ctxt>,
    {
        let changed = changes.apply(capabilities, ctxt);
        for (place, cap) in changes.iter() {
            if cap == Some(CapabilityKind::Exclusive) {
                self.label_lifetime_projections(
                    &LabelNodePredicate::all_future_postfixes(place),
                    None,
                    ctxt,
                );
            }
        }
        changed
    }

    fn edges_blocking<'slf, Ctxt: Copy + DebugCtxt>(
        &'slf self,
        node: BlockedNode<'tcx>,
        ctxt: Ctxt,
    ) -> impl Iterator<Item = BorrowPcgEdgeRef<'tcx, 'slf, EdgeKind, VC>>
    where
        EdgeKind: EdgeData<'tcx, Ctxt, Place<'tcx>> + std::hash::Hash + Eq + 'slf,
        VC: 'slf,
        'tcx: 'slf,
    {
        self.graph().edges_blocking(node, ctxt)
    }
}

impl<'pcg, 'tcx: 'pcg> BorrowsStateLike<'tcx> for BorrowStateMutRef<'pcg, 'tcx> {
    fn as_mut_ref(&mut self) -> BorrowStateMutRef<'_, 'tcx> {
        BorrowStateMutRef::new(self.graph, self.validity_conditions)
    }

    fn graph(&self) -> &BorrowsGraph<'tcx> {
        self.graph
    }

    fn as_ref(&self) -> BorrowStateRef<'_, 'tcx> {
        BorrowStateRef::new(self.graph, self.validity_conditions)
    }
}

impl<'tcx, EdgeKind: Eq + std::hash::Hash, VC> BorrowsStateLike<'tcx, EdgeKind, VC>
    for BorrowsState<'_, 'tcx, EdgeKind, VC>
{
    fn as_mut_ref(&mut self) -> BorrowStateMutRef<'_, 'tcx, EdgeKind, VC> {
        BorrowStateMutRef::new(&mut self.graph, self.validity_conditions)
    }

    fn graph(&self) -> &BorrowsGraph<'tcx, EdgeKind, VC> {
        &self.graph
    }

    fn as_ref(&self) -> BorrowStateRef<'_, 'tcx, EdgeKind, VC> {
        BorrowStateRef::new(&self.graph, self.validity_conditions)
    }
}

impl<'pcg, 'tcx> From<&'pcg mut BorrowsState<'_, 'tcx>> for BorrowStateMutRef<'pcg, 'tcx> {
    fn from(borrows_state: &'pcg mut BorrowsState<'_, 'tcx>) -> Self {
        Self::new(&mut borrows_state.graph, borrows_state.validity_conditions)
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx> + DebugCtxt> DebugLines<Ctxt>
    for BorrowsState<'_, 'tcx>
{
    fn debug_lines(&self, ctxt: Ctxt) -> Vec<Cow<'static, str>> {
        self.graph.debug_lines(ctxt)
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx> + DebugCtxt> HasValidityCheck<Ctxt>
    for BorrowStateRef<'_, 'tcx>
{
    fn check_validity(&self, ctxt: Ctxt) -> Result<(), String> {
        self.graph.check_validity(ctxt)
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx> + DebugCtxt> HasValidityCheck<Ctxt>
    for BorrowStateMutRef<'_, 'tcx>
{
    fn check_validity(&self, ctxt: Ctxt) -> Result<(), String> {
        self.as_ref().check_validity(ctxt)
    }
}

impl<EdgeKind: Eq + std::hash::Hash, VC> BorrowsState<'_, '_, EdgeKind, VC> {}

impl<'a, 'tcx> BorrowsState<'a, 'tcx, BorrowPcgEdgeKind<'tcx>, ValidityConditions> {
    fn introduce_initial_borrows(
        &mut self,
        local: mir::Local,
        capabilities: &mut impl PlaceCapabilitiesInterface<'tcx, CapabilityKind, Place<'tcx>>,
        ctxt: AnalysisCtxt<'a, 'tcx>,
    ) {
        let arg_place: Place<'tcx> = local.into();
        for region in arg_place.regions(ctxt) {
            let source_projection: LifetimeProjection<'tcx, RemotePlace> =
                LifetimeProjection::new(RemotePlace::new(local), region, None, ctxt)
                    .unwrap_or_else(|| {
                        panic!(
                            "Failed to create region for remote place (for {local:?}).
                                    It does not have region {region:?}",
                        );
                    });
            let source_projection: LifetimeProjection<'tcx, PcgLifetimeProjectionBase<'tcx>> =
                source_projection.rebase();
            let target_projection = LifetimeProjection::<'tcx, MaybeLabelledPlace<'tcx>>::new(
                MaybeLabelledPlace::Current(arg_place),
                region,
                None,
                ctxt,
            )
            .unwrap();
            assert!(
                self.apply_action(
                    &mut BorrowPcgAction::add_edge(
                        BorrowPcgEdge::new(
                            BorrowFlowEdge::new(
                                source_projection,
                                target_projection,
                                BorrowFlowEdgeKind::InitialBorrows,
                            )
                            .into(),
                            ValidityConditions::new(),
                        ),
                        "Introduce initial borrows",
                    ),
                    capabilities,
                    ctxt
                )
                .changed
            );
        }
    }

    pub(crate) fn start_block(
        capabilities: &mut impl PlaceCapabilitiesInterface<'tcx, CapabilityKind, Place<'tcx>>,
        ctxt: AnalysisCtxt<'a, 'tcx>,
    ) -> Self {
        let mut borrow = Self::default();
        for arg in ctxt.args_iter() {
            borrow.introduce_initial_borrows(arg, capabilities, ctxt);
        }
        borrow
    }
}

impl<'a, 'tcx> BorrowsState<'a, 'tcx> {
    #[must_use]
    pub fn graph(&self) -> &BorrowsGraph<'tcx> {
        &self.graph
    }

    /// The branch choices taken on every path reaching this state.
    #[must_use]
    pub fn validity_conditions(&self) -> &ValidityConditions {
        self.validity_conditions
    }

    pub(crate) fn merge(&mut self, other: &Self, ctxt: AnalysisCtxt<'a, 'tcx>) {
        self.graph.merge(&other.graph, ctxt);
        if let JoinValidityConditionsResult::Changed(new_validity_conditions) = self
            .validity_conditions
            .join_result(other.validity_conditions, ctxt.body())
        {
            self.validity_conditions = ctxt.arena.alloc(new_validity_conditions);
        }
    }

    pub(crate) fn finish_join(
        &mut self,
        args: JoinBorrowsArgs<'_, 'a, 'tcx>,
        ctxt: AnalysisCtxt<'a, 'tcx>,
    ) {
        self.graph.finish_join(self.validity_conditions, args, ctxt);
    }

    /// Remove all edges that are not valid for `path`, based on their validity
    /// conditions.
    pub fn filter_for_path(&mut self, path: &[BasicBlock], ctxt: CompilerCtxt<'_, 'tcx>) {
        self.graph.filter_for_path(path, ctxt);
    }

    pub(crate) fn edges_blocking<'slf, 'mir: 'slf>(
        &'slf self,
        node: BlockedNode<'tcx>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> Vec<BorrowPcgEdgeRef<'tcx, 'slf>> {
        self.graph.edges_blocking(node, ctxt).collect()
    }

    #[must_use]
    pub fn nodes_blocking<'slf, 'mir: 'slf>(
        &'slf self,
        node: BlockedNode<'tcx>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> HashSet<BlockingNode<'tcx>> {
        self.graph
            .edges_blocking(node, ctxt)
            .flat_map(|e| e.blocked_by_nodes(ctxt).collect::<Vec<_>>())
            .collect()
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
