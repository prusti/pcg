//! Describes the kind of Borrow PCG edges

use crate::{
    borrow_pcg::{
        borrow_pcg_expansion::BorrowPcgExpansion,
        edge::{
            abstraction::AbstractionEdge, borrow::BorrowEdge, borrow_flow::private,
            deref::DerefEdge,
        },
    },
    coupling::PcgCoupledEdgeKind,
    utils::Place,
};

use super::borrow_flow::BorrowFlowEdge;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub(crate) enum BorrowPcgEdgeKind<'tcx, P = Place<'tcx>> {
    Borrow(BorrowEdge<'tcx>),
    BorrowPcgExpansion(BorrowPcgExpansion<'tcx>),
    Deref(DerefEdge<'tcx>),
    Abstraction(AbstractionEdge<'tcx>),
    BorrowFlow(BorrowFlowEdge<'tcx, P>),
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
