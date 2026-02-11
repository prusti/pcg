use crate::{
    borrow_pcg::{
        graph::{BorrowsGraph, materialize::MaterializedEdge},
        region_projection::{LifetimeProjection, PlaceOrConst},
        state::BorrowStateRef,
    },
    owned_pcg::{OwnedPcg, OwnedPcgLocal},
    pcg::{
        CapabilityKind, MaybeHasLocation, PcgNode, PcgNodeLike, PcgRef, PositiveCapability,
        SymbolicCapability,
        place_capabilities::{PlaceCapabilities, PlaceCapabilitiesReader},
    },
    rustc_interface::{borrowck::BorrowIndex, middle::mir},
    utils::{
        CompilerCtxt, Place, PlaceLike, SnapshotLocation,
        display::{DisplayWithCompilerCtxt, DisplayWithCtxt},
    },
};

use super::{
    Graph, GraphEdge, GraphNode, NodeId, NodeType,
    grapher::{CapabilityGetter, Grapher},
    node::IdLookup,
};
use crate::{
    borrow_pcg::edge::abstraction::AbstractionEdge, utils::place::maybe_old::MaybeLabelledPlace,
};
use std::collections::{BTreeSet, HashSet};

pub(super) struct GraphConstructor<'a, 'tcx> {
    place_nodes: IdLookup<(Place<'tcx>, Option<SnapshotLocation>)>,
    region_projection_nodes: IdLookup<LifetimeProjection<'tcx>>,
    nodes: Vec<GraphNode>,
    pub(super) edges: HashSet<GraphEdge<'a>>,
    ctxt: CompilerCtxt<'a, 'tcx>,
    location: Option<mir::Location>,
}

impl<'a, 'tcx: 'a> GraphConstructor<'a, 'tcx> {
    fn new(ctxt: CompilerCtxt<'a, 'tcx>, location: Option<mir::Location>) -> Self {
        Self {
            place_nodes: IdLookup::new('p'),
            region_projection_nodes: IdLookup::new('r'),
            nodes: vec![],
            edges: HashSet::new(),
            ctxt,
            location,
        }
    }

    fn insert_maybe_labelled_place(
        &mut self,
        place: MaybeLabelledPlace<'tcx>,
        capability_getter: &impl CapabilityGetter<'a, 'tcx>,
    ) -> NodeId {
        self.insert_place_node(place.place(), place.location(), capability_getter)
    }

    fn insert_pcg_node(
        &mut self,
        node: PcgNode<'tcx>,
        capability_getter: &impl CapabilityGetter<'a, 'tcx>,
    ) -> NodeId {
        match node {
            PcgNode::Place(place) => self.insert_maybe_labelled_place(place, capability_getter),
            PcgNode::LifetimeProjection(rp) => self.insert_region_projection_node(rp),
        }
    }

    fn into_graph(self) -> Graph<'a> {
        Graph::new(self.nodes, self.edges)
    }

    fn place_node_id(&mut self, place: Place<'tcx>, location: Option<SnapshotLocation>) -> NodeId {
        self.place_nodes.node_id(&(place, location))
    }

    fn insert_node(&mut self, node: GraphNode) {
        if !self.nodes.contains(&node) {
            self.nodes.push(node);
        }
    }

    pub(super) fn insert_region_projection_node(
        &mut self,
        projection: LifetimeProjection<'tcx>,
    ) -> NodeId {
        if let Some(id) = self.region_projection_nodes.existing_id(&projection) {
            return id;
        }
        let id = self.region_projection_nodes.node_id(&projection);
        let base_ty = match projection.base() {
            PlaceOrConst::Place(p) => {
                format!("{:?}", p.related_local_place().ty(self.ctxt).ty)
            }
            PlaceOrConst::Const(c) => {
                format!("{:?}", c.ty())
            }
        };
        let loans = if let Some(output) = self.ctxt.borrow_checker.polonius_output()
            && let Some(region_vid) = projection.region(self.ctxt).vid()
        {
            let region_vid = region_vid.into();
            let render_loans = |loans: Option<&BTreeSet<BorrowIndex>>| {
                if let Some(loans) = loans {
                    format!(
                        "{{{}}}",
                        loans
                            .iter()
                            .map(|l| format!("{:?}", self.ctxt.borrow_set().unwrap()[*l].region()))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                } else {
                    "{}".to_owned()
                }
            };
            if let Some(location) = self.location {
                let location_table = self.ctxt.location_table().unwrap();
                let loans_before = render_loans(
                    output
                        .origin_contains_loan_at(location_table.start_index(location))
                        .get(&region_vid),
                );
                let loans_after = render_loans(
                    output
                        .origin_contains_loan_at(location_table.mid_index(location))
                        .get(&region_vid),
                );
                format!(
                    "Loans in {} - before: {}, mid: {}",
                    DisplayWithCtxt::<_>::display_string(&projection.region(self.ctxt), self.ctxt),
                    loans_before,
                    loans_after
                )
            } else {
                String::new()
            }
        } else {
            String::new()
        };
        let node = GraphNode {
            id,
            node_type: NodeType::RegionProjectionNode {
                label: projection.short_output(self.ctxt).into_html(),
                base_ty,
                loans,
            },
        };
        self.insert_node(node);
        id
    }

    pub(super) fn insert_abstraction(
        &mut self,
        abstraction: &AbstractionEdge<'tcx>,
        capabilities: &impl CapabilityGetter<'a, 'tcx>,
    ) {
        let input = self.insert_pcg_node(
            abstraction.input(self.ctxt).to_pcg_node(self.ctxt),
            capabilities,
        );
        let output = self.insert_pcg_node(
            abstraction.output(self.ctxt).to_pcg_node(self.ctxt),
            capabilities,
        );
        let label = match abstraction {
            AbstractionEdge::FunctionCall(fc) => fc.display_string(self.ctxt),
            AbstractionEdge::Loop(loop_abstraction) => {
                format!("loop at {:?}", loop_abstraction.location())
            }
        };
        self.edges.insert(GraphEdge::Abstract {
            blocked: input,
            blocking: output,
            label,
        });
    }

    pub(super) fn insert_place_node(
        &mut self,
        place: Place<'tcx>,
        location: Option<SnapshotLocation>,
        capability_getter: &impl CapabilityGetter<'a, 'tcx>,
    ) -> NodeId {
        if let Some(node_id) = self.place_nodes.existing_id(&(place, location)) {
            return node_id;
        }
        let capability = capability_getter.get(place);
        let id = self.place_node_id(place, location);
        let label = place.to_short_string(self.ctxt);
        let place_ty = place.ty(self.ctxt);
        let node_type = NodeType::PlaceNode {
            owned: place.is_owned(self.ctxt),
            label,
            capability: capability.and_then(|c| c.as_positive()),
            location,
            ty: format!("{:?}", place_ty.ty),
        };
        let node = GraphNode { id, node_type };
        self.insert_node(node);
        if matches!(
            capability.and_then(|c| match c {
                SymbolicCapability::Concrete(cap) => Some(cap),
                _ => None,
            }),
            Some(CapabilityKind::Read | CapabilityKind::Exclusive)
        ) {
            for rp in place.lifetime_projections(self.ctxt) {
                self.insert_region_projection_node(rp.into());
            }
        }
        id
    }
}

pub struct BorrowsGraphConstructor<'a, 'tcx, C> {
    borrows_graph: &'a BorrowsGraph<'tcx>,
    capabilities: &'a C,
    constructor: GraphConstructor<'a, 'tcx>,
    ctxt: CompilerCtxt<'a, 'tcx>,
}

impl<'a, 'tcx: 'a, C> BorrowsGraphConstructor<'a, 'tcx, C>
where
    C: PlaceCapabilitiesReader<'tcx, SymbolicCapability>,
{
    pub fn new(
        borrows_graph: &'a BorrowsGraph<'tcx>,
        capabilities: &'a C,
        ctxt: CompilerCtxt<'a, 'tcx>,
    ) -> Self {
        Self {
            borrows_graph,
            capabilities,
            constructor: GraphConstructor::new(ctxt, None),
            ctxt,
        }
    }

    pub(crate) fn construct_graph(mut self) -> Graph<'a> {
        let edges: Vec<MaterializedEdge<'tcx, 'a>> =
            self.borrows_graph.materialized_edges(self.ctxt);
        for edge in edges {
            self.draw_materialized_edge(edge);
        }
        self.constructor.into_graph()
    }
}

pub struct PcgGraphConstructor<'a, 'tcx> {
    summary: &'a OwnedPcg<'tcx>,
    borrows_domain: BorrowStateRef<'a, 'tcx>,
    capabilities: &'a PlaceCapabilities<'tcx, SymbolicCapability>,
    constructor: GraphConstructor<'a, 'tcx>,
    ctxt: CompilerCtxt<'a, 'tcx>,
}

struct PCGCapabilityGetter<'r, 'a, 'tcx, C> {
    capabilities: &'r C,
    ctxt: CompilerCtxt<'a, 'tcx>,
}

impl<'a, 'tcx, C> CapabilityGetter<'a, 'tcx> for PCGCapabilityGetter<'_, 'a, 'tcx, C>
where
    C: PlaceCapabilitiesReader<'tcx, SymbolicCapability>,
{
    fn get(&self, place: Place<'tcx>) -> Option<SymbolicCapability> {
        self.capabilities.get(place, self.ctxt)
    }
}

impl<'a, 'tcx: 'a> Grapher<'a, 'tcx> for PcgGraphConstructor<'a, 'tcx> {
    fn ctxt(&self) -> CompilerCtxt<'a, 'tcx> {
        self.ctxt
    }

    fn constructor(&mut self) -> &mut GraphConstructor<'a, 'tcx> {
        &mut self.constructor
    }

    fn capability_getter(&self) -> impl CapabilityGetter<'a, 'tcx> + 'a {
        PCGCapabilityGetter::<'a, 'a, 'tcx, _> {
            capabilities: self.capabilities,
            ctxt: self.ctxt,
        }
    }
}

impl<'a, 'tcx: 'a, C> Grapher<'a, 'tcx> for BorrowsGraphConstructor<'a, 'tcx, C>
where
    C: PlaceCapabilitiesReader<'tcx, SymbolicCapability>,
{
    fn ctxt(&self) -> CompilerCtxt<'a, 'tcx> {
        self.ctxt
    }

    fn constructor(&mut self) -> &mut GraphConstructor<'a, 'tcx> {
        &mut self.constructor
    }

    fn capability_getter(&self) -> impl CapabilityGetter<'a, 'tcx> + 'a {
        PCGCapabilityGetter::<'a, 'a, 'tcx, C> {
            capabilities: self.capabilities,
            ctxt: self.ctxt,
        }
    }
}

impl<'a, 'tcx: 'a> PcgGraphConstructor<'a, 'tcx> {
    #[must_use]
    pub fn new(
        pcg: PcgRef<'a, 'tcx>,
        ctxt: CompilerCtxt<'a, 'tcx>,
        location: mir::Location,
    ) -> Self {
        Self {
            summary: pcg.owned,
            borrows_domain: pcg.borrow,
            capabilities: pcg.capabilities,
            constructor: GraphConstructor::new(ctxt, Some(location)),
            ctxt,
        }
    }

    fn insert_place_and_previous_projections(
        &mut self,
        place: Place<'tcx>,
        location: Option<SnapshotLocation>,
        capabilities: &impl CapabilityGetter<'a, 'tcx>,
    ) -> NodeId {
        let node = self
            .constructor
            .insert_place_node(place, location, capabilities);
        if location.is_some() {
            return node;
        }
        let mut projection = place.projection;
        let mut last_node = node;
        while !projection.is_empty() {
            projection = &projection[..projection.len() - 1];
            let place = Place::new(place.local, projection);
            let node = self
                .constructor
                .insert_place_node(place, None, capabilities);
            self.constructor.edges.insert(GraphEdge::Projection {
                source: node,
                target: last_node,
            });
            last_node = node;
        }
        node
    }

    #[must_use]
    pub fn construct_graph(mut self) -> Graph<'a> {
        let capability_getter = &PCGCapabilityGetter::<'a, 'a, 'tcx, _> {
            capabilities: self.capabilities,
            ctxt: self.ctxt,
        };
        for (local, capability) in self.summary.iter_enumerated() {
            match capability {
                OwnedPcgLocal::Unallocated => {}
                OwnedPcgLocal::Allocated(projections) => {
                    self.insert_place_and_previous_projections(
                        local.into(),
                        None,
                        capability_getter,
                    );
                    for pe in projections.expansions() {
                        self.insert_place_and_previous_projections(
                            pe.place,
                            None,
                            capability_getter,
                        );
                        for child_place in pe.expansion_places(self.ctxt).unwrap() {
                            self.insert_place_and_previous_projections(
                                child_place,
                                None,
                                capability_getter,
                            );
                        }
                    }
                }
            }
        }
        for edge in self.borrows_domain.graph.materialized_edges(self.ctxt) {
            self.draw_materialized_edge(edge);
        }

        self.constructor.into_graph()
    }
}
