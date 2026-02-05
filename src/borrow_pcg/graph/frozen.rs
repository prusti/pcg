use std::cell::{Ref, RefCell};

use derive_more::{Deref, IntoIterator};
use itertools::Itertools;

use crate::{
    borrow_pcg::{
        borrow_pcg_edge::{BorrowPcgEdgeRef, LocalNode},
        edge::kind::BorrowPcgEdgeKind,
        edge_data::EdgeData,
        validity_conditions::ValidityConditions,
    },
    pcg::{PcgNode, PcgNodeLike, PcgNodeWithPlace},
    rustc_interface::data_structures::fx::{FxHashMap, FxHashSet},
    utils::{
        CompilerCtxt, DebugCtxt, HasBorrowCheckerCtxt, PcgNodeComponent, Place,
        display::DisplayWithCompilerCtxt,
    },
};

use super::BorrowsGraph;

#[derive(Deref, Clone, IntoIterator)]
pub struct CachedBlockingEdges<'graph, 'tcx>(Vec<BorrowPcgEdgeRef<'tcx, 'graph>>);

impl<'graph, 'tcx> CachedBlockingEdges<'graph, 'tcx> {
    fn new(edges: Vec<BorrowPcgEdgeRef<'tcx, 'graph>>) -> Self {
        Self(edges)
    }
}

pub(crate) type CachedLeafEdges<'graph, 'tcx> = Vec<BorrowPcgEdgeRef<'tcx, 'graph>>;

/// A data structure used for querying the Borrow PCG
///
/// It contains a reference to a Borrow PCG and mutable data structures for
/// caching intermediate query results.
pub struct FrozenGraphRef<
    'graph,
    'tcx,
    P = Place<'tcx>,
    EdgeKind = BorrowPcgEdgeKind<'tcx>,
    VC = ValidityConditions,
> {
    graph: &'graph BorrowsGraph<'tcx, EdgeKind, VC>,
    nodes_cache: RefCell<Option<FxHashSet<PcgNodeWithPlace<'tcx, P>>>>,
    edges_blocking_cache: RefCell<FxHashMap<PcgNode<'tcx>, CachedBlockingEdges<'graph, 'tcx>>>,
    leaf_edges_cache: RefCell<Option<CachedLeafEdges<'graph, 'tcx>>>,
    roots_cache: RefCell<Option<FxHashSet<PcgNode<'tcx>>>>,
}

impl<'tcx, P: PcgNodeComponent, VC> FrozenGraphRef<'_, 'tcx, P, BorrowPcgEdgeKind<'tcx, P>, VC> {
    pub(crate) fn is_leaf<'slf, Ctxt: Copy + DebugCtxt>(
        &'slf self,
        node: LocalNode<'tcx, P>,
        ctxt: Ctxt,
    ) -> bool
    where
        BorrowPcgEdgeKind<'tcx, P>: EdgeData<'tcx, Ctxt, P>,
    {
        self.graph
            .edges()
            .all(|edge| !edge.kind.blocks_node(node.into(), ctxt))
    }

    pub fn leaf_nodes<'slf, Ctxt: Copy + DebugCtxt>(
        &'slf self,
        ctxt: Ctxt,
    ) -> Vec<LocalNode<'tcx, P>>
    where
        BorrowPcgEdgeKind<'tcx, P>: EdgeData<'tcx, Ctxt, P>,
    {
        self.nodes(ctxt)
            .iter()
            .filter_map(|node| node.try_to_local_node(ctxt))
            .filter(|node| self.is_leaf(*node, ctxt))
            .collect()
    }

    pub fn nodes<'slf, Ctxt: Copy + DebugCtxt>(
        &'slf self,
        ctxt: Ctxt,
    ) -> Ref<'slf, FxHashSet<PcgNodeWithPlace<'tcx, P>>>
    where
        BorrowPcgEdgeKind<'tcx, P>: EdgeData<'tcx, Ctxt, P>,
    {
        {
            let nodes = self.nodes_cache.borrow();
            if nodes.is_some() {
                return Ref::map(nodes, |o| o.as_ref().unwrap());
            }
        }
        let nodes = self.graph.nodes(ctxt);
        self.nodes_cache.replace(Some(nodes));
        Ref::map(self.nodes_cache.borrow(), |o| o.as_ref().unwrap())
    }
}

impl<'graph, 'tcx> FrozenGraphRef<'graph, 'tcx> {
    pub(crate) fn new(graph: &'graph BorrowsGraph<'tcx>) -> Self {
        Self {
            graph,
            nodes_cache: RefCell::new(None),
            edges_blocking_cache: RefCell::new(FxHashMap::default()),
            leaf_edges_cache: RefCell::new(None),
            roots_cache: RefCell::new(None),
        }
    }

    pub(crate) fn is_acyclic<'mir: 'graph, 'bc: 'graph>(
        &mut self,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> bool {
        enum PushResult<'tcx, 'graph> {
            ExtendPath(Path<'tcx, 'graph>),
            Cycle,
        }

        #[derive(Clone, Debug, Eq, PartialEq, Hash)]
        struct Path<'tcx, 'graph>(Vec<BorrowPcgEdgeRef<'tcx, 'graph>>);

        impl<'tcx, 'graph> Path<'tcx, 'graph> {
            fn try_push(
                mut self,
                edge: BorrowPcgEdgeRef<'tcx, 'graph>,
                _ctxt: CompilerCtxt<'_, 'tcx>,
            ) -> PushResult<'tcx, 'graph> {
                if self.0.contains(&edge) {
                    PushResult::Cycle
                } else {
                    self.0.push(edge);
                    PushResult::ExtendPath(self)
                }
            }

            fn last(&self) -> BorrowPcgEdgeRef<'tcx, 'graph> {
                *self.0.last().unwrap()
            }

            fn new(edge: BorrowPcgEdgeRef<'tcx, 'graph>) -> Self {
                Self(vec![edge])
            }

            #[must_use]
            fn leads_to_cycle<'mir: 'graph, 'bc: 'graph>(
                &self,
                graph: &FrozenGraphRef<'graph, 'tcx>,
                ctxt: CompilerCtxt<'mir, 'tcx>,
            ) -> bool {
                let curr = self.last();
                let blocking_edges = curr
                    .blocked_by_nodes(ctxt)
                    .flat_map(|node| graph.get_edges_blocking(node.into(), ctxt))
                    .unique();
                for edge in blocking_edges {
                    match self.clone().try_push(edge, ctxt) {
                        PushResult::Cycle => {
                            tracing::info!("Cycle: {}", self.0.display_string(ctxt));
                            return true;
                        }
                        PushResult::ExtendPath(next_path) => {
                            if next_path.leads_to_cycle(graph, ctxt) {
                                return true;
                            }
                        }
                    }
                }
                false
            }
        }

        for node in self.nodes(ctxt).iter() {
            for edge in self.get_edges_blocking(*node, ctxt) {
                if Path::new(edge).leads_to_cycle(self, ctxt) {
                    return false;
                }
            }
        }

        true
    }

    pub fn roots<'slf, 'bc: 'graph>(
        &'slf self,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Ref<'slf, FxHashSet<PcgNode<'tcx>>> {
        {
            let roots = self.roots_cache.borrow();
            if roots.is_some() {
                return Ref::map(roots, |o| o.as_ref().unwrap());
            }
        }
        let roots = self.graph.roots(ctxt);
        self.roots_cache.replace(Some(roots));
        Ref::map(self.roots_cache.borrow(), |o| o.as_ref().unwrap())
    }

    pub fn leaf_edges<'slf, 'a: 'graph, 'bc: 'graph>(
        &'slf self,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> CachedLeafEdges<'graph, 'tcx>
    where
        'tcx: 'a,
    {
        {
            let edges = self.leaf_edges_cache.borrow();
            if edges.is_some() {
                return edges.as_ref().unwrap().clone();
            }
        }
        let edges: CachedLeafEdges<'graph, 'tcx> = self.graph.leaf_edges_set(ctxt, self);
        self.leaf_edges_cache.replace(Some(edges.clone()));
        edges
    }

    pub fn get_edges_blocking<'slf, 'mir: 'graph, 'bc: 'graph>(
        &'slf self,
        node: PcgNode<'tcx>,
        ctxt: CompilerCtxt<'mir, 'tcx>,
    ) -> CachedBlockingEdges<'graph, 'tcx> {
        {
            let map = self.edges_blocking_cache.borrow();
            if map.contains_key(&node) {
                return map[&node].clone();
            }
        }
        let edges = CachedBlockingEdges::new(self.graph.edges_blocking_set(node, ctxt));
        self.edges_blocking_cache
            .borrow_mut()
            .insert(node, edges.clone());
        edges
    }

    pub fn has_edge_blocking<'slf, 'a: 'graph, 'bc: 'graph>(
        &'slf self,
        node: PcgNode<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> bool
    where
        'tcx: 'a,
    {
        {
            let map = self.edges_blocking_cache.borrow();
            if map.contains_key(&node) {
                return !map[&node].is_empty();
            }
        }
        let edges = CachedBlockingEdges::new(self.graph.edges_blocking_set(node, ctxt));
        let result = !edges.is_empty();
        self.edges_blocking_cache.borrow_mut().insert(node, edges);
        result
    }
}
