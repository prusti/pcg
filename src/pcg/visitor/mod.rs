use crate::{
    action::{AppliedActions, BorrowPcgAction, CapabilityChanges},
    borrow_checker::r#impl::get_reserve_location,
    borrow_pcg::{
        GeneralizedLifetime,
        action::LabelPlaceReason,
        borrow_pcg_edge::{BorrowPcgEdge, BorrowPcgEdgeLike},
        edge::{
            borrow_flow::{BorrowFlowEdge, BorrowFlowEdgeKind},
            kind::BorrowPcgEdgeKind,
        },
        edge_data::LabelNodePredicate,
        region_projection::{LifetimeProjection, PcgLifetimeProjectionLike, PlaceOrConst},
    },
    owned_pcg::RepackExpand,
    pcg::{
        CapabilityKind, checks,
        ctxt::AnalysisCtxt,
        obtain::{PlaceCollapser, PlaceObtainer, expand::PlaceExpander},
        owned_state::OwnedPcg,
        place_capabilities::PlaceCapabilitiesInterface,
        triple::TripleWalker,
        visitor::upgrade::AdjustCapabilityReason,
    },
    pcg_validity_assert,
    rustc_interface::middle::mir::{self, Location, Operand, Rvalue, Statement, Terminator},
    utils::{data_structures::HashSet, display::DisplayWithCompilerCtxt},
};

use crate::utils::{
    AnalysisLocation, DataflowCtxt, HasCompilerCtxt, Place, SnapshotLocation,
    maybe_old::MaybeLabelledPlace, visitor::FallableVisitor,
};

use super::{AnalysisObject, EvalStmtPhase, Pcg, PcgNode, PcgRefLike};
use crate::error::{PcgError, PcgUnsupportedError};

mod assign;
mod function_call;
mod obtain;
mod pack;
mod stmt;
mod triple;
mod upgrade;

pub(crate) struct PcgVisitor<'pcg, 'a, 'tcx, Ctxt = AnalysisCtxt<'a, 'tcx>> {
    pcg: &'pcg mut Pcg<'a, 'tcx>,
    ctxt: Ctxt,
    actions: AppliedActions<'tcx>,
    analysis_location: AnalysisLocation,
    tw: &'pcg TripleWalker<'a, 'tcx>,
    /// For the replay check: the capability changes of the statement's
    /// post-conditions, each with the number of actions recorded before it.
    statement_effects: Vec<(usize, CapabilityChanges<Place<'tcx>>)>,
}

impl<'pcg, 'a, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> PcgVisitor<'pcg, 'a, 'tcx, Ctxt> {
    pub(crate) fn visit(
        pcg: &'pcg mut Pcg<'a, 'tcx>,
        tw: &'pcg TripleWalker<'a, 'tcx>,
        analysis_location: AnalysisLocation,
        analysis_object: AnalysisObject<'_, 'tcx>,
        ctxt: Ctxt,
    ) -> Result<AppliedActions<'tcx>, PcgError> {
        let visitor = Self::new(pcg, ctxt, tw, analysis_location);
        let actions = visitor.apply(analysis_object)?;
        Ok(actions)
    }

    pub(crate) fn new(
        pcg: &'pcg mut Pcg<'a, 'tcx>,
        ctxt: Ctxt,
        tw: &'pcg TripleWalker<'a, 'tcx>,
        analysis_location: AnalysisLocation,
    ) -> Self {
        Self {
            pcg,
            ctxt,
            actions: AppliedActions::default(),
            analysis_location,
            tw,
            statement_effects: vec![],
        }
    }

    fn prev_snapshot_location(&self) -> SnapshotLocation {
        SnapshotLocation::before(self.analysis_location)
    }

    fn phase(&self) -> EvalStmtPhase {
        self.analysis_location.eval_stmt_phase
    }

    fn location(&self) -> Location {
        self.analysis_location.location
    }

    /// Removes the borrows that the borrow checker tracks and no longer has
    /// in scope here. Such a borrow can stay in the graph while a value that
    /// flows from it lives (the regions of a type parameter in a result), but
    /// it no longer blocks its place, which gets back what the borrow took.
    /// Borrows behind a raw pointer are not tracked, and a borrow of a place
    /// that has since been overwritten blocks a labelled place: the borrow
    /// checker ends it at the write while its reference can still be used.
    fn remove_borrows_out_of_scope(&mut self) -> Result<(), PcgError> {
        let ctxt = self.ctxt;
        let location = self.location();
        let ended = self
            .pcg
            .borrow
            .graph
            .edges()
            .filter(|edge| {
                let BorrowPcgEdgeKind::Borrow(borrow) = edge.kind() else {
                    return false;
                };
                let Some(place) = borrow.blocked_place().as_current_place() else {
                    return false;
                };
                borrow.borrow_index().is_some()
                    && !place.contains_unsafe_deref(ctxt)
                    && !ctxt
                        .bc()
                        .borrows_blocking(place, location, ctxt.bc_ctxt())
                        .iter()
                        .any(|in_scope| get_reserve_location(in_scope) == borrow.reserve_location())
            })
            .map(BorrowPcgEdgeLike::to_owned_edge)
            .collect::<Vec<_>>();
        for edge in ended {
            self.place_obtainer()
                .remove_edge_and_perform_associated_state_updates(&edge, "borrow out of scope")?;
        }
        Ok(())
    }

    fn perform_borrow_initial_pre_operand_actions(&mut self) -> Result<(), PcgError> {
        self.place_obtainer()
            .pack_old_and_dead_borrow_leaves(None)?;
        for created_location in self.ctxt.bc().twophase_borrow_activations(self.location()) {
            self.activate_twophase_borrow_created_at(created_location)?;
        }
        self.remove_borrows_out_of_scope()?;
        let frozen_graph = self.pcg.borrow.graph.frozen_graph();
        let leaf_nodes = frozen_graph.leaf_nodes(self.ctxt.bc_ctxt());
        let leaf_future_node_places = leaf_nodes
            .iter()
            .filter_map(|node| match node {
                PcgNode::Place(_) => None,
                PcgNode::LifetimeProjection(region_projection) => {
                    if region_projection.is_future() {
                        region_projection.base.as_current_place()
                    } else {
                        None
                    }
                }
            })
            .collect::<HashSet<_>>();
        for place in leaf_future_node_places {
            // If the place is a leaf, and it's not borrowed, then we remove the
            // future label of a place without capability, and the freeze of a
            // frozen place ends. The latter ends a two-phase reservation of a
            // place behind a raw pointer, which the borrow checker does not
            // track and therefore never activates.
            if self.pcg.is_expansion_leaf(place, self.ctxt)
                && !self
                    .ctxt
                    .bc()
                    .is_directly_blocked(place, self.location(), self.ctxt.bc_ctxt())
            {
                match self.pcg.capability_of(place, self.ctxt) {
                    None if self
                        .pcg
                        .borrow
                        .graph
                        .edges_blocking(place.into(), self.ctxt.bc_ctxt())
                        .next()
                        .is_none() =>
                    {
                        // The edge that blocked the place would have returned
                        // its capability when it was removed.
                        let ctxt = self.ctxt;
                        pcg_validity_assert!(
                            false,
                            [ctxt],
                            "{:?}: {} is unblocked without a capability",
                            self.location(),
                            place.display_string(ctxt)
                        );
                        self.record_and_apply_action(
                            BorrowPcgAction::label_lifetime_projection(
                                LabelNodePredicate::all_future_postfixes(place),
                                None,
                                "Leaf future node: remove future label",
                            )
                            .into(),
                        )?;
                    }
                    Some(CapabilityKind::Read)
                        if self.place_obtainer().frozen_ancestor(place) == place =>
                    {
                        self.place_obtainer().end_freeze(
                            place,
                            None,
                            AdjustCapabilityReason::UnborrowedFutureNode,
                        )?;
                    }
                    _ => {}
                }
            }
        }
        Ok(())
    }

    pub(crate) fn apply(
        mut self,
        object: AnalysisObject<'_, 'tcx>,
    ) -> Result<AppliedActions<'tcx>, PcgError> {
        let before = checks::enabled().then(|| self.pcg.place_capabilities.clone());
        self.apply_phase(object)?;
        if let Some(before) = before {
            let mut steps = vec![];
            let mut effects = self.statement_effects.iter().peekable();
            for (index, applied) in self.actions.iter().enumerate() {
                while let Some((_, effect)) = effects.next_if(|(at, _)| *at <= index) {
                    steps.push(effect);
                }
                steps.push(checks::listed_changes(&applied.action));
            }
            steps.extend(effects.map(|(_, effect)| effect));
            checks::replay::check(
                &format!("{:?} {:?}", self.location(), self.phase()),
                &before,
                steps,
                &self.pcg.place_capabilities,
                self.ctxt.bc_ctxt(),
            );
            checks::state::check(self.pcg, self.location(), self.ctxt.bc_ctxt());
        }
        Ok(self.actions)
    }

    fn apply_phase(&mut self, object: AnalysisObject<'_, 'tcx>) -> Result<(), PcgError> {
        match self.phase() {
            EvalStmtPhase::PreOperands => {
                self.perform_borrow_initial_pre_operand_actions()?;
                self.place_obtainer().collapse_owned_places()?;
                for triple in &self.tw.operand_triples {
                    tracing::debug!("Require triple {triple:?}");
                    self.require_triple(*triple)?;
                }
            }
            EvalStmtPhase::PostOperands => {
                for triple in &self.tw.operand_triples {
                    self.ensure_triple(*triple)?;
                }
            }
            EvalStmtPhase::PreMain => {
                for triple in &self.tw.main_triples {
                    tracing::debug!("Require triple {triple:?}");
                    self.require_triple(*triple)?;
                }
            }
            EvalStmtPhase::PostMain => {
                for triple in &self.tw.main_triples {
                    self.ensure_triple(*triple)?;
                }
            }
        }
        let location = self.location();
        match object {
            AnalysisObject::Statement(statement) => {
                self.visit_statement_fallable(statement, location)?;
            }
            AnalysisObject::Terminator(terminator) => {
                self.visit_terminator_fallable(terminator, location)?;
                if self.phase() == EvalStmtPhase::PostMain {
                    // when the analysis object is a terminator, this step ensures
                    // the owned PCG is in the most-packed state for the join.
                    self.place_obtainer().collapse_owned_places()?;
                }
            }
        }
        Ok(())
    }

    fn outlives_generalized(
        &self,
        sup: GeneralizedLifetime<'tcx>,
        sub: GeneralizedLifetime<'tcx>,
    ) -> bool {
        self.ctxt
            .bc()
            .outlives_generalized(sup, sub, self.location())
    }

    fn connect_outliving_projections(
        &mut self,
        source_proj: LifetimeProjection<'tcx, PlaceOrConst<'tcx, MaybeLabelledPlace<'tcx>>>,
        target: Place<'tcx>,
        kind: impl Fn(GeneralizedLifetime<'tcx>) -> BorrowFlowEdgeKind<'tcx>,
    ) -> Result<(), PcgError> {
        let ctxt = self.ctxt;
        for target_proj in target.lifetime_projections(self.ctxt) {
            let source_region = source_proj.region(ctxt.ctxt());
            let target_region = target_proj.region(ctxt.ctxt());
            if self.outlives_generalized(source_region, target_region) {
                self.record_and_apply_action(
                    BorrowPcgAction::add_edge(
                        BorrowPcgEdge::new(
                            BorrowFlowEdge::new(
                                source_proj.to_pcg_lifetime_projection(),
                                target_proj.into(),
                                kind(target_region),
                            )
                            .into(),
                            self.pcg.borrow.validity_conditions.clone(),
                        ),
                        "connect_outliving_projections",
                    )
                    .into(),
                )?;
            }
            // A future edge of the source says that what is written into its
            // region through a mutable borrow becomes the borrowed place's
            // future value. The moved value holds those writes only in a
            // target region equal to the source's (the same position below
            // the mutable reference), not in one the source merely
            // outlives, such as the lifetime of a reference to it.
            if let PlaceOrConst::Place(base) = source_proj.base
                && self.outlives_generalized(source_region, target_region)
                && self.outlives_generalized(target_region, source_region)
            {
                let local_source_proj = source_proj.with_base(base);
                self.place_obtainer().redirect_source_of_future_edges(
                    local_source_proj,
                    target_proj.into(),
                    ctxt,
                )?;
            }
        }
        Ok(())
    }
}

impl<'a, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> FallableVisitor<'tcx>
    for PcgVisitor<'_, 'a, 'tcx, Ctxt>
{
    #[tracing::instrument(skip(self, _location))]
    fn visit_statement_fallable(
        &mut self,
        statement: &Statement<'tcx>,
        _location: Location,
    ) -> Result<(), PcgError> {
        self.perform_statement_actions(statement)
    }

    fn visit_operand_fallable(
        &mut self,
        operand: &Operand<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        if let Operand::Move(place) = operand
            && self.phase() == EvalStmtPhase::PostOperands
        {
            let snapshot_location = self.prev_snapshot_location();
            self.record_and_apply_action(
                BorrowPcgAction::label_place_and_update_related_capabilities(
                    (*place).into(),
                    snapshot_location,
                    LabelPlaceReason::MoveOut,
                )
                .into(),
            )?;
        }
        self.super_operand_fallable(operand, location);
        Ok(())
    }

    fn visit_terminator_fallable(
        &mut self,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        self.super_terminator_fallable(terminator, location)?;
        if self.phase() == EvalStmtPhase::PostMain
            && let mir::TerminatorKind::Call {
                func,
                args,
                destination,
                fn_span,
                ..
            } = &terminator.kind
        {
            let destination: Place<'tcx> = (*destination).into();
            self.make_function_call_abstraction(
                func,
                *fn_span,
                &args.iter().map(|arg| &arg.node).collect::<Vec<_>>(),
                destination,
                location,
            )?;
        }
        Ok(())
    }

    fn visit_place_fallable(
        &mut self,
        _place: Place<'tcx>,
        _context: mir::visit::PlaceContext,
        _location: Location,
    ) {
    }

    fn visit_rvalue_fallable(
        &mut self,
        rvalue: &Rvalue<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        if matches!(rvalue, Rvalue::Ref(_, mir::BorrowKind::Fake(_), _)) {
            return Ok(());
        }
        self.super_rvalue_fallable(rvalue, location)?;
        Ok(())
    }
}

impl<'state, 'a: 'state, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>>
    PlaceObtainer<'state, 'a, 'tcx, Ctxt>
{
    /// The places that must not be collapsed here because they are part of the
    /// loop invariant. For example, if the loop invariant requires `x.f` but
    /// NOT `x.g`, then `x` must not be collapsed (because the loop invariant
    /// does not provide permission to `x.g`).
    fn places_required_by_enclosing_loops(&self) -> Vec<Place<'tcx>> {
        self.ctxt
            .body_analysis()
            .places_required_by_enclosing_loops(self.location().block)
            .collect()
    }

    fn collapse_iteration(
        &mut self,
        local: mir::Local,
        iteration: usize,
        places_to_keep_unpacked: &[Place<'tcx>],
    ) -> Result<bool, PcgError> {
        let local_expansions = self.pcg.owned[local].expansions();
        let parent_places = local_expansions.places_expanded_only_to_leaves(self.ctxt);
        let places_to_collapse = parent_places
            .into_iter()
            .filter(|place| {
                !places_to_keep_unpacked
                    .iter()
                    .any(|required| place.is_strict_prefix_of(*required))
            })
            .filter_map(|place| {
                let expansion_places = local_expansions.all_children_of(place, self.ctxt);
                if expansion_places
                    .iter()
                    .all(|p| !self.pcg.borrow.graph.contains(*p, self.ctxt.bc_ctxt()))
                    && let Some(candidate_cap) = self
                        .pcg
                        .place_capabilities
                        .uniform_capability(expansion_places.into_iter(), self.ctxt)
                {
                    Some((place, candidate_cap))
                } else {
                    None
                }
            })
            .collect::<HashSet<_>>();
        if places_to_collapse.is_empty() {
            return Ok(false);
        }
        for (place, candidate_cap) in places_to_collapse {
            self.collapse_owned_places_and_lifetime_projections_to(
                place,
                candidate_cap,
                format!(
                    "Collapse owned place {} (iteration {})",
                    place.display_string(self.ctxt),
                    iteration
                ),
                self.ctxt,
            )?;
            if place.projection.is_empty()
                && self.pcg.capability_of(place, self.ctxt) == Some(CapabilityKind::Read)
                && !self
                    .ctxt
                    .body_analysis()
                    .is_read_only_in_loop(self.location().block, place)
                && !self
                    .blocked_owned_places(self.ctxt.bc_ctxt())
                    .contains(&place)
            {
                self.record_and_apply_action(
                    BorrowPcgAction::unfreeze(place, "unfreeze collapsed local").into(),
                )?;
            }
        }
        Ok(true)
    }
}

impl<'state, 'a: 'state, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>>
    PlaceObtainer<'state, 'a, 'tcx, Ctxt>
{
    pub(crate) fn collapse_owned_places(&mut self) -> Result<(), PcgError> {
        let allocated_locals = self.pcg.owned.allocated_locals();
        let places_to_keep_unpacked = self.places_required_by_enclosing_loops();
        for local in allocated_locals {
            self.iterations_for_local(local, &places_to_keep_unpacked)?;
        }
        Ok(())
    }

    fn iterations_for_local(
        &mut self,
        local: mir::Local,
        places_to_keep_unpacked: &[Place<'tcx>],
    ) -> Result<(), PcgError> {
        let mut iteration = 1;
        while self.collapse_iteration(local, iteration, places_to_keep_unpacked)? {
            iteration += 1;
        }
        Ok(())
    }
}

impl<'a, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> PcgVisitor<'_, 'a, 'tcx, Ctxt> {
    fn activate_twophase_borrow_created_at(
        &mut self,
        created_location: Location,
    ) -> Result<(), PcgError> {
        let Some(borrow) = self.pcg.borrow_created_at(created_location) else {
            return Ok(());
        };
        tracing::info!(
            "{:?} activate twophase borrow: {}",
            self.location(),
            borrow.display_string(self.ctxt)
        );
        // A reservation of a labelled place (an old value, such as that of a
        // dead reference labelled at a loop head) has no capability to take:
        // it is activated without changing any.
        let Some(blocked_place) = borrow.blocked_place.as_current_place() else {
            let borrow = borrow.clone();
            return self.record_and_apply_action(
                BorrowPcgAction::activate_two_phase_borrow(borrow, "activate two-phase borrow")
                    .into(),
            );
        };
        let ctxt = self.ctxt;
        if !self
            .pcg
            .place_capability_equals(blocked_place, CapabilityKind::Read, ctxt)
        {
            pcg_validity_assert!(
                false,
                [ctxt],
                "Activating a two-phase borrow of {} with capability {:?}",
                blocked_place.display_string(ctxt),
                self.pcg.capability_of(blocked_place, ctxt)
            );
            return Ok(());
        }
        let borrow = borrow.clone();
        // If the place is a read copy of a frozen ancestor (the ancestor was
        // read during the reservation, or the reservation was made under a
        // shared borrow of it), the freeze moves to the place first.
        let frozen = self.place_obtainer().frozen_ancestor(blocked_place);
        if frozen != blocked_place {
            self.place_obtainer().end_freeze(
                frozen,
                Some(blocked_place),
                AdjustCapabilityReason::TwoPhaseBorrowActivation,
            )?;
        }
        self.place_obtainer()
            .detach_borrowed_untracked_referents(blocked_place, &|_| false)?;
        self.place_obtainer()
            .pack_read_unpacking(blocked_place, &|_| false)?;
        // Reads during the reservation may have unpacked the place at R.
        if blocked_place.as_owned_place(self.ctxt).is_some() {
            let ctxt = self.ctxt;
            self.place_obtainer()
                .collapse_owned_places_and_lifetime_projections_to(
                    blocked_place,
                    CapabilityKind::Read,
                    "pack the reads of a two-phase borrowed place".to_owned(),
                    ctxt,
                )?;
        }
        // The read copies that are left go with the place.
        let dropped = self
            .place_obtainer()
            .read_copies_to_drop(blocked_place)
            .into_iter()
            .map(|p| (p, None))
            .collect::<Vec<_>>();
        self.record_and_apply_action(
            BorrowPcgAction::activate_two_phase_borrow(borrow, "activate two-phase borrow")
                .with_capabilities(dropped.into())
                .into(),
        )?;
        self.place_obtainer().label_rps_up_to(
            blocked_place,
            frozen,
            AdjustCapabilityReason::TwoPhaseBorrowActivation,
        )?;
        Ok(())
    }
}

impl<'tcx> OwnedPcg<'tcx> {
    pub(crate) fn perform_expand_action<'a, Ctxt: HasCompilerCtxt<'a, 'tcx>>(
        &mut self,
        expand: RepackExpand<'tcx>,
        capabilities: &mut impl PlaceCapabilitiesInterface<'tcx>,
        ctxt: Ctxt,
    ) -> CapabilityChanges<Place<'tcx>>
    where
        'tcx: 'a,
    {
        let expansions = self[expand.local()].expansions_mut();
        expansions.perform_expand_action(expand, capabilities, ctxt)
    }
}
