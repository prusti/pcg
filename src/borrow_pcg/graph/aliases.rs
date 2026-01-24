use crate::{
    borrow_pcg::{
        borrow_pcg_edge::{BorrowPcgEdgeRef, LocalNode},
        edge::{borrow_flow::BorrowFlowEdgeKind, kind::BorrowPcgEdgeKind},
        edge_data::EdgeData,
    },
    pcg::{LocalNodeLike, PcgNode, PcgNodeLike},
    rustc_interface::data_structures::fx::FxHashSet,
    utils::{CompilerCtxt, PlaceProjectable, data_structures::HashSet},
};

use super::BorrowsGraph;

#[derive(Eq, PartialEq, Hash, Debug)]
#[allow(dead_code)]
struct Alias<'tcx> {
    node: PcgNode<'tcx>,
    exact_alias: bool,
}

impl<'tcx> BorrowsGraph<'tcx> {
    pub(crate) fn ancestor_edges<'graph, 'a: 'graph>(
        &'graph self,
        node: LocalNode<'tcx>,
        ctxt: CompilerCtxt<'a, 'tcx>,
    ) -> FxHashSet<BorrowPcgEdgeRef<'tcx, 'graph>> {
        let mut result: FxHashSet<BorrowPcgEdgeRef<'tcx, 'graph>> = FxHashSet::default();
        let mut stack = vec![node];
        let mut seen: FxHashSet<PcgNode<'tcx>> = FxHashSet::default();
        while let Some(node) = stack.pop() {
            if seen.insert(node.into()) {
                for edge in self.edges_blocked_by(node, ctxt) {
                    result.insert(edge);
                    for node in edge.blocked_nodes(ctxt) {
                        if let Some(local_node) = node.try_to_local_node(ctxt) {
                            stack.push(local_node);
                        }
                    }
                }
            }
        }
        result
    }
    pub(crate) fn aliases(
        &self,
        node: LocalNode<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx, ()>,
    ) -> FxHashSet<PcgNode<'tcx>> {
        let mut result: FxHashSet<PcgNode<'tcx>> = FxHashSet::default();
        result.insert(node.into());
        let mut stack = vec![node];
        while let Some(node) = stack.pop() {
            for alias in self.aliases_all_projections(node, ctxt) {
                if result.insert(alias)
                    && let Some(local_node) = alias.try_to_local_node(ctxt)
                {
                    stack.push(local_node);
                }
            }
        }
        result
    }

    fn aliases_all_projections(
        &self,
        node: LocalNode<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx, ()>,
    ) -> FxHashSet<PcgNode<'tcx>> {
        let mut results: FxHashSet<Alias<'tcx>> = FxHashSet::default();
        for (place, proj) in node.iter_projections(ctxt) {
            results.insert(Alias {
                node: place.into(),
                exact_alias: true,
            });
            let candidates: Vec<_> = results.drain().collect();
            for alias in candidates {
                if !alias.exact_alias {
                    continue;
                }
                let local_node = if let Some(local_node) = alias.node.try_to_local_node(ctxt) {
                    local_node
                } else {
                    continue;
                };
                let local_node = if let Ok(n) = local_node.project_deeper(proj, ctxt) {
                    n
                } else {
                    continue;
                };
                results.extend(self.direct_aliases(
                    local_node,
                    ctxt,
                    &mut FxHashSet::default(),
                    true,
                ));
                if let PcgNode::Place(p) = local_node
                    && let Some(rp) = p.deref_to_rp(ctxt)
                {
                    for node in self.nodes(ctxt) {
                        if let Some(PcgNode::LifetimeProjection(p)) = node.try_to_local_node(ctxt)
                            && p.base() == rp.base()
                            && p.region_idx == rp.region_idx
                        {
                            results.extend(self.direct_aliases(
                                p.to_local_node(ctxt),
                                ctxt,
                                &mut FxHashSet::default(),
                                true,
                            ));
                        }
                    }
                }
            }
        }
        results.into_iter().map(|a| a.node).collect()
    }

    #[tracing::instrument(skip(self, ctxt, seen, direct))]
    fn direct_aliases(
        &self,
        node: LocalNode<'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx, ()>,
        seen: &mut FxHashSet<PcgNode<'tcx>>,
        direct: bool,
    ) -> FxHashSet<Alias<'tcx>> {
        let mut result = HashSet::default();
        result.insert(Alias {
            node: node.into(),
            exact_alias: direct,
        });

        let extend = |blocked: PcgNode<'tcx>,
                      seen: &mut FxHashSet<PcgNode<'tcx>>,
                      result: &mut FxHashSet<Alias<'tcx>>,
                      exact_alias: bool| {
            if seen.insert(blocked) {
                result.insert(Alias {
                    node: blocked,
                    exact_alias,
                });
                if let Some(local_node) = blocked.try_to_local_node(ctxt) {
                    result.extend(self.direct_aliases(local_node, ctxt, seen, exact_alias));
                }
            }
        };

        for edge in self.edges_blocked_by(node, ctxt) {
            match edge.kind {
                BorrowPcgEdgeKind::Deref(deref_edge) => {
                    let blocked = deref_edge.deref_place;
                    extend(blocked.into(), seen, &mut result, direct);
                }
                BorrowPcgEdgeKind::Borrow(borrow_edge) => {
                    let blocked = borrow_edge.blocked_place();
                    extend(blocked.into(), seen, &mut result, direct);
                }
                BorrowPcgEdgeKind::BorrowPcgExpansion(e) => {
                    for node in e.blocked_nodes(ctxt) {
                        if let PcgNode::LifetimeProjection(p) = node {
                            extend(p.to_pcg_node(ctxt), seen, &mut result, false);
                        }
                    }
                }
                BorrowPcgEdgeKind::Abstraction(abstraction_type) => {
                    extend(
                        abstraction_type.input(ctxt).to_pcg_node(ctxt),
                        seen,
                        &mut result,
                        false,
                    );
                }
                BorrowPcgEdgeKind::BorrowFlow(outlives) => match &outlives.kind {
                    BorrowFlowEdgeKind::Assignment(_) => {
                        extend(outlives.long().to_pcg_node(ctxt), seen, &mut result, true);
                    }
                    BorrowFlowEdgeKind::BorrowOutlives { regions_equal }
                        if !regions_equal || direct => {}
                    _ => {
                        extend(outlives.long().to_pcg_node(ctxt), seen, &mut result, false);
                    }
                },
                BorrowPcgEdgeKind::Coupled(edges) => {
                    for input in edges.inputs(ctxt) {
                        extend(input.0, seen, &mut result, false);
                    }
                }
            }
        }
        result
    }
}
