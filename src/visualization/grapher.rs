use crate::{
    borrow_pcg::{
        borrow_pcg_edge::BorrowPcgEdgeRef,
        edge::kind::BorrowPcgEdgeKind,
        edge_data::EdgeData,
        graph::materialize::{MaterializedEdge, SyntheticEdge},
    },
    pcg::{MaybeHasLocation, PcgNode, PcgNodeLike, SymbolicCapability},
    rustc_interface::middle::mir,
    utils::{CompilerCtxt, HasPlace, Place, maybe_old::MaybeLabelledPlace},
};

use super::{GraphEdge, NodeId, graph_constructor::GraphConstructor};

pub(super) trait CapabilityGetter<'a, 'tcx: 'a> {
    fn get(&self, node: Place<'tcx>) -> Option<SymbolicCapability>;
}

pub(super) trait Grapher<'a, 'tcx: 'a> {
    fn capability_getter(&self) -> impl CapabilityGetter<'a, 'tcx> + 'a;
    fn insert_maybe_labelled_place(&mut self, place: MaybeLabelledPlace<'tcx>) -> NodeId {
        let capability_getter = self.capability_getter();
        let constructor = self.constructor();
        constructor.insert_place_node(place.place(), place.location(), &capability_getter)
    }
    fn insert_pcg_node(&mut self, node: PcgNode<'tcx>) -> NodeId {
        match node {
            PcgNode::Place(place) => self.insert_maybe_labelled_place(place),
            PcgNode::LifetimeProjection(rp) => self.constructor().insert_region_projection_node(rp),
        }
    }

    fn constructor(&mut self) -> &mut GraphConstructor<'a, 'tcx>;
    fn ctxt(&self) -> CompilerCtxt<'a, 'tcx>;
    fn draw_materialized_edge(&mut self, edge: MaterializedEdge<'tcx, 'a>) {
        match edge {
            MaterializedEdge::Real(edge) => {
                self.draw_borrow_pcg_edge(edge, &self.capability_getter())
            }
            MaterializedEdge::Synthetic(edge) => self.draw_synthetic_edge(edge),
        }
    }
    fn draw_synthetic_edge(&mut self, edge: SyntheticEdge<'tcx>) {
        match edge {
            SyntheticEdge::Alias(edge) => {
                let blocked_place = self.insert_pcg_node(edge.blocked_place);
                let blocking_place = self.insert_pcg_node(edge.blocking_place);
                self.constructor().edges.insert(GraphEdge::Alias {
                    blocked_place,
                    blocking_place,
                });
            }
        }
    }
    fn draw_borrow_pcg_edge(
        &mut self,
        edge: BorrowPcgEdgeRef<'tcx, 'a>,
        capabilities: &impl CapabilityGetter<'a, 'tcx>,
    ) {
        let validity_conditions = edge.conditions;
        match edge.kind() {
            BorrowPcgEdgeKind::Deref(deref_edge) => {
                let deref_place = self.insert_pcg_node(deref_edge.deref_place.into());
                for blocked in deref_edge.blocked_nodes(self.ctxt()) {
                    let blocked = self.insert_pcg_node(blocked);
                    self.constructor().edges.insert(GraphEdge::DerefExpansion {
                        source: blocked,
                        target: deref_place,
                        validity_conditions,
                    });
                }
            }
            BorrowPcgEdgeKind::BorrowPcgExpansion(deref_expansion) => {
                for blocked in deref_expansion.blocked_nodes(self.ctxt()) {
                    let blocked_graph_node = self.insert_pcg_node(blocked);
                    for blocking in deref_expansion.blocked_by_nodes(self.ctxt()) {
                        let blocking_graph_node = self.insert_pcg_node(blocking.into());
                        self.constructor().edges.insert(GraphEdge::DerefExpansion {
                            source: blocked_graph_node,
                            target: blocking_graph_node,
                            validity_conditions,
                        });
                    }
                }
            }
            BorrowPcgEdgeKind::Borrow(borrow) => {
                let borrowed_place = self.insert_maybe_labelled_place(borrow.blocked_place());
                let assigned_region_projection = borrow
                    .assigned_lifetime_projection(self.ctxt())
                    .to_lifetime_projection();
                let assigned_rp_node = self
                    .constructor()
                    .insert_region_projection_node(assigned_region_projection);
                let kind = match borrow.kind() {
                    mir::BorrowKind::Shared => "shared".to_owned(),
                    mir::BorrowKind::Mut { kind } => format!("{kind:?}"),
                    mir::BorrowKind::Fake(_) => "fake".to_owned(),
                };
                self.constructor().edges.insert(GraphEdge::Borrow {
                    borrowed_place,
                    assigned_region_projection: assigned_rp_node,
                    location: borrow.reserve_location(),
                    region: format!("{:?}", borrow.region),
                    validity_conditions,
                    kind,
                    borrow_index: borrow.borrow_index().map(|i| format!("{i:?}")),
                });
            }
            BorrowPcgEdgeKind::Abstraction(abstraction) => {
                self.constructor()
                    .insert_abstraction(abstraction, capabilities);
            }
            BorrowPcgEdgeKind::BorrowFlow(member) => {
                let input_node = self.insert_pcg_node(member.long().to_pcg_node(self.ctxt()));
                let output_node = self.insert_pcg_node(member.short().to_pcg_node(self.ctxt()));
                self.constructor().edges.insert(GraphEdge::BorrowFlow {
                    source: input_node,
                    target: output_node,
                    kind: member.kind,
                });
            }
            BorrowPcgEdgeKind::Coupled(hyper_edge) => {
                for input in hyper_edge.inputs(self.ctxt()) {
                    let input_node = self.insert_pcg_node(input.0);
                    for output in hyper_edge.outputs() {
                        let output_node = self.insert_pcg_node(output.to_pcg_node(self.ctxt()));
                        self.constructor().edges.insert(GraphEdge::Coupled {
                            source: input_node,
                            target: output_node,
                        });
                    }
                }
            }
        }
    }
}
