use super::PcgVisitor;

use crate::{
    action::{BorrowPcgAction, OwnedPcgAction},
    borrow_pcg::{
        borrow_pcg_edge::BorrowPcgEdgeLike,
        edge::kind::BorrowPcgEdgeKind, region_projection::HasRegions,
    },
    owned_pcg::RepackOp,
    pcg::{
        CapabilityKind, OwnedCapability, PcgRefLike, PositiveCapability,
        place_capabilities::PlaceCapabilitiesReader,
    },
    rustc_interface::middle::mir::{Statement, StatementKind},
    utils::Place,
};

use crate::utils::{DataflowCtxt, visitor::FallableVisitor};

use super::{EvalStmtPhase, PcgError};

impl<'a, 'tcx: 'a, Ctxt: DataflowCtxt<'a, 'tcx>> PcgVisitor<'_, 'a, 'tcx, Ctxt> {
    pub(crate) fn perform_statement_actions(
        &mut self,
        statement: &Statement<'tcx>,
    ) -> Result<(), PcgError<'tcx>> {
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

    fn stmt_pre_main(&mut self, statement: &Statement<'tcx>) -> Result<(), PcgError<'tcx>> {
        assert!(self.phase() == EvalStmtPhase::PreMain);
        match &statement.kind {
            StatementKind::Assign(box (target, _)) => {
                let target = Place::from_mir_place(*target, self.ctxt);
                // Any references to target should be made old because it
                // will be overwritten in the assignment.
                if target.is_ref(self.ctxt)
                    && self
                        .pcg
                        .borrow
                        .graph()
                        .contains(target, self.ctxt.bc_ctxt())
                {
                    // The permission to the target may have been Read originally.
                    // Now, because it's been made old, the non-old place should be a leaf,
                    // and its permission should be Exclusive.
                    if self
                        .pcg
                        .place_capability_equals(target, PositiveCapability::Read, self.ctxt)
                    {
                        self.record_and_apply_action(
                            BorrowPcgAction::restore_capability(
                                target,
                                PositiveCapability::Exclusive,
                                "Assign: restore capability to exclusive",
                            )
                            .into(),
                        )?;
                    }
                }

                if let Some(target) = target.as_owned_place(self.ctxt)
                    && let Some(owned_cap) = self.pcg.owned.owned_capability(target)
                    && owned_cap > OwnedCapability::Uninitialized
                {
                    self.record_and_apply_action(
                        OwnedPcgAction::new(
                            RepackOp::weaken(target, owned_cap, OwnedCapability::Uninitialized),
                            None,
                        )
                        .into(),
                    )?;
                } else if let Some(target_cap) = self.pcg.get(target, self.ctxt).into_positive()
                    && CapabilityKind::<()>::Write < target_cap
                {
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
                for rp in target.lifetime_projections(self.ctxt).into_iter() {
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
                        }
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn stmt_post_main(&mut self, statement: &Statement<'tcx>) -> Result<(), PcgError<'tcx>> {
        assert!(self.phase() == EvalStmtPhase::PostMain);
        if let StatementKind::Assign(box (target, rvalue)) = &statement.kind {
            self.assign_post_main(Place::from_mir_place(*target, self.ctxt), rvalue)?;
        }
        Ok(())
    }
}
