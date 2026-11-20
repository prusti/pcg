use std::{borrow::Cow, rc::Rc};

use crate::{
    DebugLines,
    action::PcgActions,
    borrow_pcg::{graph::BorrowsGraph, state::BorrowsState},
    rustc_interface::middle::mir::BasicBlock,
    utils::{DebugCtxt, HasBorrowCheckerCtxt},
};

/// The CFG edge from a terminator to `block`. Its `actions` apply to the
/// terminator's state after its main effect (`PostMain`), or, on the unwind
/// edge of a call, to the state before it (`PreMain`). In order, they are: on
/// the unwind edge of a call, the effect of the unwinding call, which uses its
/// arguments but does not assign its destination; on an edge into a cleanup
/// block, the expiry of the borrows that end on the edge, with the
/// restorations and collapses it allows; the repacks to the owned places of
/// `block`'s entry state; at a loop head, the place expansions of its entry
/// state; and the additions of the entry state's abstraction edges that the
/// source state (after the effect of an unwinding call) lacks, compared
/// without their conditions. The entry state's borrow graph is `entry_graph`.
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

impl<'a, 'tcx: 'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx> + DebugCtxt> DebugLines<Ctxt>
    for PcgSuccessor<'a, 'tcx>
{
    fn debug_lines(&self, ctxt: Ctxt) -> Vec<Cow<'static, str>> {
        self.actions.iter().map(|a| a.debug_line(ctxt)).collect()
    }
}
