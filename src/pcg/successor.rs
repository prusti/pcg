use std::rc::Rc;

use serde_json::json;

use crate::{
    DebugLines,
    action::PcgActions,
    borrow_checker::BorrowCheckerInterface,
    borrow_pcg::{graph::BorrowsGraph, state::BorrowsState},
    rustc_interface::middle::mir::BasicBlock,
    utils::{
        CompilerCtxt, HasBorrowCheckerCtxt,
        json::{ToJsonWithCompilerCtxt, ToJsonWithCtxt},
    },
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

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>> ToJsonWithCtxt<Ctxt>
    for PcgSuccessor<'a, 'tcx>
{
    fn to_json(&self, repacker: Ctxt) -> serde_json::Value {
        json!({
            "block": self.block().index(),
            "actions": self.actions.to_json(repacker),
        })
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
