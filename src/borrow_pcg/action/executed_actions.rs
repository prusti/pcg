use crate::borrow_pcg::action::BorrowPCGAction;
use crate::borrow_pcg::action::actions::BorrowPCGActions;
use crate::utils::CompilerCtxt;

#[derive(Debug, Clone)]
pub(crate) struct ExecutedActions<'tcx> {
    actions: BorrowPCGActions<'tcx>,
}

impl<'tcx> ExecutedActions<'tcx> {
    pub(crate) fn new() -> Self {
        Self {
            actions: BorrowPCGActions::new(),
        }
    }

    pub(crate) fn record(&mut self, action: BorrowPCGAction<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) {
        self.actions.push(action, ctxt);
    }

    pub(crate) fn extend(&mut self, actions: ExecutedActions<'tcx>) {
        self.actions.extend(actions.actions);
    }

    pub(crate) fn actions(self) -> BorrowPCGActions<'tcx> {
        self.actions
    }
}
