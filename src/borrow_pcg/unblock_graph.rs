//! Data structures and algorithms related to [`UnblockGraph`].
use std::marker::PhantomData;

use derive_more::From;

use crate::{
    borrow_pcg::borrow_pcg_edge::{BorrowPcgEdge, BorrowPcgEdgeRef},
    error::PcgInternalError,
    utils::{HasBorrowCheckerCtxt, data_structures::HashSet},
};

use super::borrow_pcg_edge::{BlockedNode, BorrowPcgEdgeLike};
use crate::{
    borrow_pcg::{edge_data::EdgeData, state::BorrowsState},
    utils::CompilerCtxt,
};

type UnblockEdge<'tcx> = BorrowPcgEdge<'tcx>;

/// A subgraph of the Borrow PCG including the edges that should be removed
/// in order to unblock a given node.
#[derive(Clone, Debug)]
pub struct UnblockGraph<'tcx, Edge = UnblockEdge<'tcx>> {
    edges: HashSet<Edge>,
    _marker: PhantomData<&'tcx ()>,
}

/// An action that removes an edge from the Borrow PCG
#[derive(Clone, Debug, Eq, PartialEq, From)]
pub struct BorrowPcgUnblockAction<'tcx, Edge = BorrowPcgEdge<'tcx>> {
    pub(super) edge: Edge,
    _marker: PhantomData<&'tcx ()>,
}

impl<'tcx, Edge> BorrowPcgUnblockAction<'tcx, Edge> {
    pub fn new(edge: Edge) -> Self {
        Self {
            edge,
            _marker: PhantomData,
        }
    }
    pub fn edge(&self) -> &Edge {
        &self.edge
    }
}

impl<'tcx, Edge: std::fmt::Debug + Clone + Eq + std::hash::Hash> UnblockGraph<'tcx, Edge> {
    /// Returns an ordered list of actions to unblock the edges in the graph.
    /// This is essentially a topological sort of the edges.
    pub fn actions<'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>>(
        self,
        ctxt: Ctxt,
    ) -> Result<Vec<BorrowPcgUnblockAction<'tcx, Edge>>, PcgInternalError>
    where
        'tcx: 'a,
        Edge: EdgeData<'tcx, Ctxt>,
    {
        let mut edges = self.edges;
        let mut actions = vec![];

        while !edges.is_empty() {
            let mut to_keep = edges.clone();

            let should_kill_edge = |edge: &Edge| {
                edge.blocked_by_nodes(ctxt)
                    .all(|node| edges.iter().all(|e| !e.blocks_node(node.into(), ctxt)))
            };
            for edge in edges.iter() {
                if should_kill_edge(edge) {
                    actions.push(BorrowPcgUnblockAction::new(edge.clone()));
                    to_keep.remove(edge);
                }
            }
            if to_keep.len() >= edges.len() {
                return Err(PcgInternalError::new(format!(
                    "Didn't remove any leaves {edges:#?}"
                )));
            }
            edges = to_keep;
        }
        Ok(actions)
    }
}

impl<'tcx> UnblockGraph<'tcx> {
    pub(crate) fn new() -> Self {
        Self {
            edges: HashSet::default(),
            _marker: PhantomData,
        }
    }

    pub fn for_node(
        node: impl Into<BlockedNode<'tcx>>,
        state: &BorrowsState<'_, 'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Self {
        Self::for_nodes(vec![node], state, ctxt)
    }

    pub fn for_nodes(
        nodes: impl IntoIterator<Item = impl Into<BlockedNode<'tcx>>>,
        state: &BorrowsState<'_, 'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Self {
        let mut ug = Self::new();
        for node in nodes {
            ug.unblock_node(node.into(), state, ctxt);
        }
        ug
    }

    pub fn is_empty(&self) -> bool {
        self.edges.is_empty()
    }

    fn add_dependency(&mut self, unblock_edge: UnblockEdge<'tcx>) -> bool {
        self.edges.insert(unblock_edge)
    }

    pub(crate) fn kill_edge<
        'a,
        Edge: BorrowPcgEdgeLike<'tcx> + EdgeData<'tcx, Ctxt>,
        Ctxt: Copy + HasBorrowCheckerCtxt<'a, 'tcx>,
    >(
        &mut self,
        edge: Edge,
        borrows: &BorrowsState<'a, 'tcx>,
        ctxt: Ctxt,
    ) where
        'tcx: 'a,
    {
        if self.add_dependency(edge.clone().to_owned_edge()) {
            for blocking_node in edge.blocked_by_nodes(ctxt) {
                self.unblock_node(blocking_node.into(), borrows, ctxt.bc_ctxt());
            }
        }
    }

    #[tracing::instrument(skip(self, borrows, ctxt))]
    pub(crate) fn unblock_node<'a: 'slf, 'slf, Ctxt: Copy + HasBorrowCheckerCtxt<'a, 'tcx>>(
        &'slf mut self,
        node: BlockedNode<'tcx>,
        borrows: &'slf BorrowsState<'a, 'tcx>,
        ctxt: Ctxt,
    ) where
        'tcx: 'a,
        BorrowPcgEdgeRef<'tcx, 'slf>: EdgeData<'tcx, Ctxt>,
    {
        for edge in borrows.edges_blocking(node, ctxt.bc_ctxt()) {
            self.kill_edge(edge, borrows, ctxt);
        }
    }
}
