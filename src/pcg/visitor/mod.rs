use crate::{
    action::{AppliedActions, BorrowPcgAction, PcgAction},
    borrow_pcg::{
        action::LabelPlaceReason,
        borrow_pcg_edge::BorrowPcgEdge,
        edge::borrow_flow::{BorrowFlowEdge, BorrowFlowEdgeKind},
        region_projection::{
            LifetimeProjection, PcgLifetimeProjectionLike, PcgRegion, PlaceOrConst,
        },
    },
    error::CallWithUnsafePtrWithNestedLifetime,
    owned_pcg::{OwnedPcg, RepackExpand},
    pcg::{
        CapabilityKind, PcgRefLike, PositiveCapability,
        ctxt::AnalysisCtxt,
        obtain::{PlaceCollapser, PlaceObtainer, expand::PlaceExpander},
        place_capabilities::PlaceCapabilitiesReader,
        triple::TripleWalker,
        visitor::upgrade::AdjustCapabilityReason,
    },
    rustc_interface::middle::mir::{self, Location, Operand, Rvalue, Statement, Terminator},
    utils::{data_structures::HashSet, display::DisplayWithCompilerCtxt},
};

use crate::utils::{
    self, AnalysisLocation, DataflowCtxt, HasCompilerCtxt, Place, SnapshotLocation,
    maybe_old::MaybeLabelledPlace, visitor::FallableVisitor,
};

use super::{AnalysisObject, EvalStmtPhase, Pcg, PcgNode};
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
}

impl<'pcg, 'a, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> PcgVisitor<'pcg, 'a, 'tcx, Ctxt> {
    pub(crate) fn capability(&self, place: Place<'tcx>) -> CapabilityKind {
        self.pcg
            .owned
            .capability(place, &self.pcg.borrow.graph, self.ctxt)
    }
    pub(crate) fn visit(
        pcg: &'pcg mut Pcg<'a, 'tcx>,
        tw: &'pcg TripleWalker<'a, 'tcx>,
        analysis_location: AnalysisLocation,
        analysis_object: AnalysisObject<'_, 'tcx>,
        ctxt: Ctxt,
    ) -> Result<AppliedActions<'tcx>, PcgError<'tcx>> {
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

    fn perform_borrow_initial_pre_operand_actions(&mut self) -> Result<(), PcgError<'tcx>> {
        self.place_obtainer()
            .pack_old_and_dead_borrow_leaves(None)?;
        for created_location in self.ctxt.bc().twophase_borrow_activations(self.location()) {
            self.activate_twophase_borrow_created_at(created_location)?;
        }
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
            // If the place is a leaf, and its not borrowed, then we remove the future label
            if self.pcg.is_expansion_leaf(place, self.ctxt)
                && !self
                    .ctxt
                    .bc()
                    .is_directly_blocked(place, self.location(), self.ctxt.bc_ctxt())
                && self.capability(place).is_none()
            {
                let action = PcgAction::restore_capability(
                    place,
                    PositiveCapability::Exclusive,
                    "Leaf future node restore cap",
                    self.ctxt,
                );
                self.record_and_apply_action(action)?;
            }
        }
        Ok(())
    }

    pub(crate) fn apply(
        mut self,
        object: AnalysisObject<'_, 'tcx>,
    ) -> Result<AppliedActions<'tcx>, PcgError<'tcx>> {
        match self.phase() {
            EvalStmtPhase::PreOperands => {
                self.perform_borrow_initial_pre_operand_actions()?;
                self.place_obtainer().collapse_owned_places()?;
                for triple in &self.tw.operand_triples {
                    tracing::debug!("Require triple {:?}", triple);
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
                    tracing::debug!("Require triple {:?}", triple);
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
        Ok(self.actions)
    }

    fn outlives(&self, sup: PcgRegion<'tcx>, sub: PcgRegion<'tcx>) -> bool {
        self.ctxt.bc().outlives(sup, sub, self.location())
    }

    fn connect_outliving_projections(
        &mut self,
        source_proj: LifetimeProjection<'tcx, PlaceOrConst<'tcx, MaybeLabelledPlace<'tcx>>>,
        target: Place<'tcx>,
        kind: impl Fn(PcgRegion) -> BorrowFlowEdgeKind<'tcx>,
    ) -> Result<(), PcgError<'tcx>> {
        let ctxt = self.ctxt;
        for target_proj in target.lifetime_projections(self.ctxt).into_iter() {
            if self.outlives(
                source_proj.region(ctxt.ctxt()),
                target_proj.region(ctxt.ctxt()),
            ) {
                self.record_and_apply_action(
                    BorrowPcgAction::add_edge(
                        BorrowPcgEdge::new(
                            BorrowFlowEdge::new(
                                source_proj.to_pcg_lifetime_projection(),
                                target_proj.into(),
                                kind(target_proj.region(self.ctxt.ctxt())),
                            )
                            .into(),
                            self.pcg.borrow.validity_conditions.clone(),
                        ),
                        "connect_outliving_projections",
                    )
                    .into(),
                )?;
            }
            if let PlaceOrConst::Place(base) = source_proj.base {
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
    ) -> Result<(), PcgError<'tcx>> {
        self.perform_statement_actions(statement)
    }

    fn visit_operand_fallable(
        &mut self,
        operand: &Operand<'tcx>,
        location: Location,
    ) -> Result<(), PcgError<'tcx>> {
        match operand {
            Operand::Copy(place) => {
                let place: Place<'tcx> = (*place).into();
                if let Err(e) = place.check_lifetimes_under_unsafe_ptr(self.ctxt) {
                    return Err(PcgError::unsupported(
                        PcgUnsupportedError::MoveUnsafePtrWithNestedLifetime(e),
                    ));
                }
            }
            Operand::Move(place) => {
                if self.phase() == EvalStmtPhase::PostOperands {
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
            }
            _ => {}
        }
        self.super_operand_fallable(operand, location)?;
        Ok(())
    }

    fn visit_terminator_fallable(
        &mut self,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) -> Result<(), PcgError<'tcx>> {
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
            for operand in args {
                if let Some(place) = operand.node.place() {
                    let place: utils::Place<'tcx> = place.into();
                    if let Err(e) = place.check_lifetimes_under_unsafe_ptr(self.ctxt) {
                        let function = format!("{func:?}");
                        if function != "std::io::_print" {
                            let err = CallWithUnsafePtrWithNestedLifetime {
                                function: format!("{func:?}"),
                                span: *fn_span,
                                place: e,
                            };
                            return Err(PcgUnsupportedError::CallWithUnsafePtrWithNestedLifetime(
                                err,
                            )
                            .into());
                        }
                    }
                }
            }
            let destination: utils::Place<'tcx> = (*destination).into();
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
        place: utils::Place<'tcx>,
        _context: mir::visit::PlaceContext,
        _location: Location,
    ) -> Result<(), PcgError<'tcx>> {
        if place.contains_unsafe_deref(self.ctxt) {
            tracing::error!(
                "DerefUnsafePtr: {}",
                place.display_string(self.ctxt.bc_ctxt())
            );
            return Err(PcgError::unsupported(PcgUnsupportedError::DerefUnsafePtr));
        }
        Ok(())
    }

    fn visit_rvalue_fallable(
        &mut self,
        rvalue: &Rvalue<'tcx>,
        location: Location,
    ) -> Result<(), PcgError<'tcx>> {
        if matches!(rvalue, Rvalue::Ref(_, mir::BorrowKind::Fake(_), _)) {
            return Ok(());
        }
        self.super_rvalue_fallable(rvalue, location)?;
        Ok(())
    }
}

impl<'state, 'a: 'state, 'tcx: 'a, Ctxt> PlaceObtainer<'state, 'a, 'tcx, Ctxt> {
    fn collapse_iteration<'slf>(
        &'slf mut self,
        local: mir::Local,
        iteration: usize,
    ) -> Result<bool, PcgError<'tcx>>
    where
        Ctxt: DataflowCtxt<'a, 'tcx>,
    {
        let local_expansions = self.pcg.owned[local].get_allocated();
        let leaf_expansions = local_expansions.leaf_expansions(local.into(), self.ctxt);
        let parent_places = leaf_expansions
            .iter()
            .map(|pe| pe.base_place)
            .collect::<HashSet<_>>();
        let places_to_collapse = parent_places
            .into_iter()
            .filter_map(|place| {
                let expansion_places = local_expansions.all_children_of(place, self.ctxt);
                if expansion_places
                    .iter()
                    .all(|p| !self.pcg.borrow.graph.contains(*p, self.ctxt.bc_ctxt()))
                    && let Some(candidate_cap) = self
                        .pcg
                        .as_ref()
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
            let _span = tracing::span!(tracing::Level::WARN, "collapse_iteration",
            place = place.display_string(self.ctxt.bc_ctxt()),
            candidate_cap = ?candidate_cap
            )
            .entered();
            self.collapse_owned_places_and_lifetime_projections_to(
                place,
                candidate_cap.into_positive().unwrap(),
                format!(
                    "Collapse owned place {} (iteration {})",
                    place.display_string(self.ctxt.bc_ctxt()),
                    iteration
                ),
                self.ctxt,
            )?;
        }
        Ok(true)
    }
}

impl<'state, 'a: 'state, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>>
    PlaceObtainer<'state, 'a, 'tcx, Ctxt>
{
    pub(crate) fn collapse_owned_places(&mut self) -> Result<(), PcgError<'tcx>> {
        let allocated_locals = self.pcg.owned.allocated_locals();
        for local in allocated_locals {
            self.iterations_for_local(local)?;
        }
        Ok(())
    }

    fn iterations_for_local(&mut self, local: mir::Local) -> Result<(), PcgError<'tcx>> {
        let mut iteration = 1;
        while self.collapse_iteration(local, iteration)? {
            iteration += 1;
        }
        Ok(())
    }
}

impl<'a, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> PcgVisitor<'_, 'a, 'tcx, Ctxt> {
    fn activate_twophase_borrow_created_at(
        &mut self,
        created_location: Location,
    ) -> Result<(), PcgError<'tcx>> {
        let Some(borrow) = self.pcg.borrow_created_at(created_location) else {
            return Ok(());
        };
        tracing::info!(
            "{:?} activate twophase borrow: {}",
            self.location(),
            borrow.display_string(self.ctxt.bc_ctxt())
        );
        let blocked_place = borrow.blocked_place.place();
        self.place_obtainer()
            .remove_read_permission_upwards_and_label_rps(
                blocked_place,
                AdjustCapabilityReason::TwoPhaseBorrowActivation,
            )?;
        Ok(())
    }
}

impl<'tcx> OwnedPcg<'tcx> {
    pub(crate) fn perform_expand_action<'a, Ctxt: HasCompilerCtxt<'a, 'tcx>>(
        &mut self,
        expand: RepackExpand<'tcx>,
        ctxt: Ctxt,
    ) where
        'tcx: 'a,
    {
        let expansions = self[expand.local()].get_allocated_mut();
        expansions.perform_expand_action(expand, ctxt);
    }
}
