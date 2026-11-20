//! Describes the kind of Borrow PCG edges

use crate::{
    borrow_pcg::{
        borrow_pcg_expansion::BorrowPcgExpansion,
        edge::{
            abstraction::AbstractionEdge, borrow::BorrowEdge, borrow_flow::private,
            delegation::DelegationEdge, deref::DerefEdge, rawptr_deref::RawPtrDerefEdge,
        },
    },
    coupling::PcgCoupledEdgeKind,
    utils::Place,
};

use super::borrow_flow::BorrowFlowEdge;

#[derive(Clone, Debug, Eq, PartialEq, Hash, pcg_macros::DisplayWithCtxt)]
pub enum BorrowPcgEdgeKind<'tcx, P = Place<'tcx>> {
    Borrow(BorrowEdge<'tcx, P>),
    BorrowPcgExpansion(BorrowPcgExpansion<'tcx, P>),
    Deref(DerefEdge<'tcx, P>),
    Abstraction(AbstractionEdge<'tcx, P>),
    BorrowFlow(BorrowFlowEdge<'tcx, P>),
    Coupled(PcgCoupledEdgeKind<'tcx, P>),
    Delegation(DelegationEdge<'tcx, P>),
    RawPtrDeref(RawPtrDerefEdge<'tcx, P>),
}

impl<P> BorrowPcgEdgeKind<'_, P> {
    /// Whether the edge lends the places it blocks (a borrow, a call, a loop),
    /// rather than unpacking them or aliasing them by a raw pointer.
    pub(crate) fn is_loan(&self) -> bool {
        !matches!(
            self,
            Self::Deref(_)
                | Self::RawPtrDeref(_)
                | Self::BorrowPcgExpansion(_)
                | Self::Delegation(_)
        )
    }
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
    Delegation,
    RawPtrDeref,
}
