use std::rc::Rc;

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
    pub fn actions(&self) -> &PcgActions<'tcx> {
        &self.actions
    }
    pub fn block(&self) -> BasicBlock {
        self.block
    }
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
    fn debug_lines(&self, repacker: CompilerCtxt<'_, 'tcx>) -> Vec<String> {
        let mut result = Vec::new();
        result.push(format!("Block: {}", self.block().index()));
        result.extend(self.actions.iter().map(|a| a.debug_line(repacker)));
        result
    }
}
