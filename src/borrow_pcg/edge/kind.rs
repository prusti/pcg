//! Describes the kind of Borrow PCG edges

use crate::{
    borrow_pcg::{
        borrow_pcg_expansion::BorrowPcgExpansion,
        edge::{abstraction::AbstractionEdge, borrow::BorrowEdge, deref::DerefEdge},
    },
    utils::CompilerCtxt,
};

use super::{borrow::RemoteBorrow, outlives::BorrowFlowEdge};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum BorrowPcgEdgeKind<'tcx> {
    Borrow(BorrowEdge<'tcx>),
    BorrowPcgExpansion(BorrowPcgExpansion<'tcx>),
    Deref(DerefEdge<'tcx>),
    Abstraction(AbstractionEdge<'tcx>),
    BorrowFlow(BorrowFlowEdge<'tcx>),
}

impl<'tcx> From<RemoteBorrow<'tcx>> for BorrowPcgEdgeKind<'tcx> {
    fn from(borrow: RemoteBorrow<'tcx>) -> Self {
        BorrowPcgEdgeKind::Borrow(BorrowEdge::Remote(borrow))
    }
}

impl<'tcx> BorrowPcgEdgeKind<'tcx> {
    pub(crate) fn is_shared_borrow(&self, repacker: CompilerCtxt<'_, 'tcx>) -> bool {
        match self {
            BorrowPcgEdgeKind::Borrow(reborrow) => !reborrow.is_mut(repacker),
            _ => false,
        }
    }
}
