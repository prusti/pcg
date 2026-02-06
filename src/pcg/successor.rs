use std::{borrow::Cow, rc::Rc};

use crate::{
    DebugLines,
    action::PcgActions,
    borrow_pcg::{graph::BorrowsGraph, state::BorrowsState},
    rustc_interface::middle::mir::BasicBlock,
    utils::CompilerCtxt,
};

#[derive(Debug)]
pub struct PcgSuccessor<'a, 'tcx> {
    block: BasicBlock,
    pub(crate) actions: PcgActions<'tcx>,
    entry_state: Rc<BorrowsState<'a, 'tcx>>,
}

impl<'a, 'tcx> PcgSuccessor<'a, 'tcx> {
    #[must_use]
    pub fn actions(&self) -> &PcgActions<'tcx> {
        &self.actions
    }
    #[must_use]
    pub fn block(&self) -> BasicBlock {
        self.block
    }
    #[must_use]
    pub fn entry_graph(&self) -> &BorrowsGraph<'tcx> {
        self.entry_state.graph()
    }
    pub(crate) fn new(
        block: BasicBlock,
        actions: PcgActions<'tcx>,
        entry_state: Rc<BorrowsState<'a, 'tcx>>,
    ) -> Self {
        Self {
            block,
            actions,
            entry_state,
        }
    }
}

impl<'tcx> DebugLines<CompilerCtxt<'_, 'tcx>> for PcgSuccessor<'_, 'tcx> {
    fn debug_lines(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> Vec<Cow<'static, str>> {
        let mut result = Vec::new();
        result.extend(self.actions.iter().map(|a| a.debug_line(ctxt)));
        result
    }
}
