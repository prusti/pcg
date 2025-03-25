use std::rc::Rc;

use crate::{
    combined_pcs::PcgError,
    rustc_interface::{
        borrowck::PoloniusOutput,
        middle::{
            mir::{Body, Location, Statement, Terminator, TerminatorEdges},
            ty::TyCtxt,
        },
    },
    utils::{display::DisplayDiff, visitor::FallableVisitor},
};

use super::{
    state::BorrowsState,
    visitor::{BorrowsVisitor, StatementStage},
};
use crate::borrow_pcg::domain::BorrowsDomain;
use crate::utils::eval_stmt_data::EvalStmtData;
use crate::utils::PlaceRepacker;

pub struct BorrowsEngine<'mir, 'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) body: &'mir Body<'tcx>,
    pub(crate) output_facts: Option<&'mir PoloniusOutput>,
}

impl<'mir, 'tcx> BorrowsEngine<'mir, 'tcx> {
    pub(crate) fn new(
        tcx: TyCtxt<'tcx>,
        body: &'mir Body<'tcx>,
        output_facts: Option<&'mir PoloniusOutput>,
    ) -> Self {
        BorrowsEngine {
            tcx,
            body,
            output_facts,
        }
    }
}

impl<'a, 'tcx> BorrowsEngine<'a, 'tcx> {
    #[tracing::instrument(skip(self,state,statement), fields(block = ?state.block()))]
    pub(crate) fn prepare_operands(
        &mut self,
        state: &mut BorrowsDomain<'a, 'tcx>,
        statement: &Statement<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        state.data.enter_transfer_fn();

        state.data.states.0.pre_operands = state.data.states.0.post_main.clone();
        BorrowsVisitor::preparing(self, state, StatementStage::Operands)
            .visit_statement_fallable(statement, location)?;

        if !state.actions.pre_operands.is_empty() {
            state.data.states.0.pre_operands = state.data.states.0.post_main.clone();
        } else if state.data.states.0.pre_operands != state.data.states.0.post_main {
            panic!(
                "{:?}: No actions were emitted, but the state has changed:\n{}",
                location,
                state.data.states.0.pre_operands.fmt_diff(
                    state.data.states.0.post_main.as_ref(),
                    PlaceRepacker::new(self.body, self.tcx)
                )
            );
        }
        Ok(())
    }

    pub(crate) fn apply_operands(
        &mut self,
        state: &mut BorrowsDomain<'a, 'tcx>,
        statement: &Statement<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        BorrowsVisitor::applying(self, state, StatementStage::Operands)
            .visit_statement_fallable(statement, location)?;
        state.data.states.0.post_operands = state.data.states.0.post_main.clone();
        Ok(())
    }
    pub(crate) fn prepare_statement_effect(
        &mut self,
        state: &mut BorrowsDomain<'a, 'tcx>,
        statement: &Statement<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        BorrowsVisitor::preparing(self, state, StatementStage::Main)
            .visit_statement_fallable(statement, location)?;
        state.data.states.0.pre_main = state.data.states.0.post_main.clone();
        Ok(())
    }

    pub(crate) fn apply_statement_effect(
        &mut self,
        state: &mut BorrowsDomain<'a, 'tcx>,
        statement: &Statement<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        BorrowsVisitor::applying(self, state, StatementStage::Main)
            .visit_statement_fallable(statement, location)
    }

    #[tracing::instrument(skip(self, state, terminator))]
    pub(crate) fn apply_before_terminator_effect(
        &mut self,
        state: &mut BorrowsDomain<'a, 'tcx>,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) -> Result<(), PcgError> {
        state.data.enter_transfer_fn();
        BorrowsVisitor::preparing(self, state, StatementStage::Operands)
            .visit_terminator_fallable(terminator, location)?;
        state.data.pre_operands_complete();
        BorrowsVisitor::applying(self, state, StatementStage::Operands)
            .visit_terminator_fallable(terminator, location)?;
        state.data.post_operands_complete();
        Ok(())
    }

    pub(crate) fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut BorrowsDomain<'a, 'tcx>,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> Result<TerminatorEdges<'mir, 'tcx>, PcgError> {
        BorrowsVisitor::preparing(self, state, StatementStage::Main)
            .visit_terminator_fallable(terminator, location)?;
        state.data.pre_main_complete();
        BorrowsVisitor::applying(self, state, StatementStage::Main)
            .visit_terminator_fallable(terminator, location)?;
        Ok(terminator.edges())
    }
}

pub(crate) type BorrowsStates<'tcx> = EvalStmtData<Rc<BorrowsState<'tcx>>>;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) enum DataflowPhase {
    Init,
    Join,
    Transfer,
}
