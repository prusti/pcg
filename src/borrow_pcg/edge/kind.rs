//! Describes the kind of Borrow PCG edges

use crate::{
    borrow_pcg::{
        borrow_pcg_expansion::BorrowPcgExpansion,
        edge::{
            abstraction::AbstractionEdge, borrow::BorrowEdge, deref::DerefEdge, outlives::private,
        },
    },
    coupling::PcgCoupledEdgeKind,
};

use super::outlives::BorrowFlowEdge;

#[derive(Clone, Debug, Eq, PartialEq, Hash, pcg_macros::DisplayWithCtxt)]
pub enum BorrowPcgEdgeKind<'tcx> {
    Borrow(BorrowEdge<'tcx>),
    BorrowPcgExpansion(BorrowPcgExpansion<'tcx>),
    Deref(DerefEdge<'tcx>),
    Abstraction(AbstractionEdge<'tcx>),
    BorrowFlow(BorrowFlowEdge<'tcx>),
    Coupled(PcgCoupledEdgeKind<'tcx>),
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum BorrowPcgEdgeType {
    Borrow,
    BorrowPcgExpansion,
    Deref,
    Abstraction,
    BorrowFlow {
        future_edge_kind: Option<private::FutureEdgeKind>,
    },
    Coupled,
}
