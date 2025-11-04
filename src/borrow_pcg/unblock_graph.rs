//! Data structures and algorithms related to [`UnblockGraph`].
use std::marker::PhantomData;

use derive_more::From;

use crate::{
    borrow_pcg::borrow_pcg_edge::BorrowPcgEdge, error::PcgInternalError,
    utils::data_structures::HashSet,
};

use super::borrow_pcg_edge::{BlockedNode, BorrowPcgEdgeLike};
use crate::{
    borrow_pcg::{edge_data::EdgeData, state::BorrowsState},
    utils::CompilerCtxt,
};

use crate::coupling::{MaybeCoupledEdgeKind, PcgCoupledEdges};

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

impl<'tcx, Edge: EdgeData<'tcx> + std::fmt::Debug + Clone + Eq + std::hash::Hash>
    UnblockGraph<'tcx, Edge>
{
    /// Returns an ordered list of actions to unblock the edges in the graph.
    /// This is essentially a topological sort of the edges.
    pub fn actions(
        self,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Result<Vec<BorrowPcgUnblockAction<'tcx, Edge>>, PcgInternalError> {
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

    #[allow(unused)]
    pub(crate) fn into_coupled(
        mut self,
    ) -> UnblockGraph<'tcx, MaybeCoupledEdgeKind<'tcx, BorrowPcgEdge<'tcx>>> {
        use crate::coupling::MaybeCoupledEdges;

        let coupled = PcgCoupledEdges::extract_from_data_source(&mut self.edges);
        let mut edges: HashSet<MaybeCoupledEdgeKind<'tcx, BorrowPcgEdge<'tcx>>> = self
            .edges
            .into_iter()
            .map(MaybeCoupledEdgeKind::NotCoupled)
            .collect();
        edges.extend(
            coupled
                .into_maybe_coupled_edges()
                .into_iter()
                .flat_map(|edge| match edge {
                    MaybeCoupledEdges::Coupled(coupled) => coupled
                        .edges()
                        .into_iter()
                        .map(MaybeCoupledEdgeKind::Coupled)
                        .collect::<Vec<_>>(),
                    MaybeCoupledEdges::NotCoupled(not_coupled) => not_coupled
                        .into_iter()
                        .map(|edge| MaybeCoupledEdgeKind::NotCoupled(edge.into()))
                        .collect::<Vec<_>>(),
                }),
        );
        UnblockGraph {
            edges,
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

    pub(crate) fn kill_edge(
        &mut self,
        edge: impl BorrowPcgEdgeLike<'tcx>,
        borrows: &BorrowsState<'_, 'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) {
        if self.add_dependency(edge.clone().to_owned_edge()) {
            for blocking_node in edge.blocked_by_nodes(ctxt) {
                self.unblock_node(blocking_node.into(), borrows, ctxt);
            }
        }
    }

    #[tracing::instrument(skip(self, borrows, ctxt))]
    pub(crate) fn unblock_node(
        &mut self,
        node: BlockedNode<'tcx>,
        borrows: &BorrowsState<'_, 'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) {
        for edge in borrows.edges_blocking(node, ctxt) {
            self.kill_edge(edge, borrows, ctxt);
        }
    }
}
