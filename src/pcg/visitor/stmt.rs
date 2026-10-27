use super::PcgVisitor;

use crate::{
    action::BorrowPcgAction,
    borrow_pcg::{
        action::LabelPlaceReason, borrow_pcg_edge::BorrowPcgEdgeLike, edge::kind::BorrowPcgEdgeKind,
    },
    pcg::{CapabilityKind, PcgRefLike},
    pcg_validity_assert,
    rustc_interface::middle::mir::{Statement, StatementKind},
    utils::{self, DataflowCtxt, visitor::FallableVisitor},
};

use super::{EvalStmtPhase, PcgError};

impl<'a, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> PcgVisitor<'_, 'a, 'tcx, Ctxt> {
    pub(crate) fn perform_statement_actions(
        &mut self,
        statement: &Statement<'tcx>,
    ) -> Result<(), PcgError> {
        self.super_statement_fallable(statement, self.location())?;
        match self.phase() {
            EvalStmtPhase::PreMain => {
                self.stmt_pre_main(statement)?;
            }
            EvalStmtPhase::PostMain => {
                self.stmt_post_main(statement)?;
            }
            _ => {}
        }
        Ok(())
    }

    fn stmt_pre_main(&mut self, statement: &Statement<'tcx>) -> Result<(), PcgError> {
        assert_eq!(self.phase(), EvalStmtPhase::PreMain);
        match &statement.kind {
            StatementKind::StorageLive(local) => {
                let ctxt = self.ctxt;
                let location = self.location();
                pcg_validity_assert!(
                    !self.pcg.owned.is_allocated(*local),
                    [ctxt at location],
                    "StorageLive({local:?}) called while the local is already allocated in the PCG"
                );
            }
            StatementKind::StorageDead(local) => {
                let place: utils::Place<'tcx> = (*local).into();
                let snapshot_location = self.prev_snapshot_location();
                self.record_and_apply_action(
                    BorrowPcgAction::label_place_and_update_related_capabilities(
                        place,
                        snapshot_location,
                        LabelPlaceReason::StorageDead,
                    )
                    .into(),
                )?;
            }
            StatementKind::Assign(box (target, _)) => {
                let target: utils::Place<'tcx> = (*target).into();
                // Any references to target should be made old because it
                // will be overwritten in the assignment.
                if target.is_ref(self.ctxt)
                    && self
                        .pcg
                        .borrow
                        .graph()
                        .contains(target, self.ctxt.bc_ctxt())
                {
                    // The target may have been frozen originally. Now, because
                    // its dereference has been made old, the freeze ends.
                    if self.pcg.capability_of(target, self.ctxt) == Some(CapabilityKind::Read) {
                        self.place_obtainer()
                            .upgrade_read_to_exclusive(target, &|_| false)?;
                    }
                }

                if let Some(target_cap) = self.pcg.capability_of(target, self.ctxt) {
                    pcg_validity_assert!(
                        target_cap >= CapabilityKind::Write,
                        "target_cap: {:?}",
                        target_cap
                    );
                    if target_cap != CapabilityKind::Write {
                        self.record_and_apply_action(
                            BorrowPcgAction::weaken(
                                target,
                                target_cap,
                                CapabilityKind::Write,
                                "pre_main",
                            )
                            .into(),
                        )?;
                    }
                }
                let mut removed_edges = Vec::new();
                for rp in target.lifetime_projections(self.ctxt) {
                    let blocked_edges = self
                        .pcg
                        .borrow
                        .graph()
                        .edges_blocked_by(rp.into(), self.ctxt.bc_ctxt())
                        .map(BorrowPcgEdgeLike::to_owned_edge)
                        .collect::<Vec<_>>();
                    for edge in blocked_edges {
                        let should_remove =
                            !matches!(edge.kind(), BorrowPcgEdgeKind::BorrowPcgExpansion(_));
                        if should_remove {
                            self.place_obtainer()
                                .remove_edge_and_perform_associated_state_updates(
                                    &edge, "Assign",
                                )?;
                            removed_edges.push(edge);
                        }
                    }
                }
                self.place_obtainer()
                    .finish_weakening_places_with_dead_lifetime_projections(&removed_edges)?;
            }
            _ => {}
        }
        Ok(())
    }

    fn stmt_post_main(&mut self, statement: &Statement<'tcx>) -> Result<(), PcgError> {
        assert_eq!(self.phase(), EvalStmtPhase::PostMain);
        if let StatementKind::Assign(box (target, rvalue)) = &statement.kind {
            self.assign_post_main((*target).into(), rvalue)?;
        }
        Ok(())
    }
}
