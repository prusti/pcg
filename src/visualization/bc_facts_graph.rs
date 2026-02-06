use std::{cell::RefCell, collections::BTreeMap};

use itertools::Itertools;
use petgraph::graph::NodeIndex;

use crate::{
    borrow_checker::{RustBorrowCheckerInterface, r#impl::PoloniusBorrowChecker},
    borrow_pcg::{region_projection::OverrideRegionDebugString, visitor::extract_regions},
    rustc_interface::{
        borrowck::{PoloniusRegionVid, RegionInferenceContext},
        middle::{
            mir::{Body, Location},
            ty::{self, RegionVid},
        },
    },
    utils::{
        CompilerCtxt,
        callbacks::RustBorrowCheckerImpl,
        display::{DisplayOutput, DisplayWithCompilerCtxt, DisplayWithCtxt, OutputMode},
    },
};

use super::{
    dot_graph::{DotEdge, DotGraph, DotNode, EdgeDirection, EdgeOptions},
    node::IdLookup,
};

impl<Ctxt: OverrideRegionDebugString> DisplayWithCtxt<Ctxt> for PoloniusRegionVid {
    fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
        let region: RegionVid = (*self).into();
        region.display_output(ctxt, mode)
    }
}

fn get_id<Ctxt, T: Clone + Eq + DisplayWithCtxt<Ctxt>>(
    elem: &T,
    nodes: &mut IdLookup<T>,
    graph_nodes: &mut Vec<DotNode>,
    ctxt: Ctxt,
) -> String {
    if let Some(id) = nodes.existing_id(elem) {
        id.to_string()
    } else {
        let id = nodes.node_id(elem);
        graph_nodes.push(DotNode::simple(id.to_string(), elem.display_string(ctxt)));
        id.to_string()
    }
}

pub fn subset_anywhere<'a, 'tcx: 'a, 'bc>(
    ctxt: CompilerCtxt<'a, 'tcx, &'bc PoloniusBorrowChecker<'a, 'tcx>>,
) -> DotGraph {
    let mut graph = DotGraph {
        nodes: vec![],
        edges: vec![],
        name: "bcfacts".into(),
    };
    let mut nodes = IdLookup::new('n');
    for loc in ctxt.borrow_checker.output_facts.subset.values() {
        for (sup, subs) in loc {
            let sup_node = get_id(sup, &mut nodes, &mut graph.nodes, ctxt);
            for sub in subs {
                let sub_node = get_id(sub, &mut nodes, &mut graph.nodes, ctxt);
                let edge = DotEdge {
                    id: None,
                    from: sup_node.to_string(),
                    to: sub_node.to_string(),
                    options: EdgeOptions::directed(EdgeDirection::Forward),
                };
                if !graph.edges.contains(&edge) {
                    graph.edges.push(edge);
                }
            }
        }
    }
    graph
}

#[derive(Clone)]
pub struct RegionPrettyPrinter<'bc, 'tcx> {
    sccs: RefCell<Option<petgraph::Graph<Vec<RegionVid>, ()>>>,
    region_to_string: BTreeMap<RegionVid, String>,
    #[allow(dead_code)]
    region_infer_ctxt: &'bc RegionInferenceContext<'tcx>,
}

impl OverrideRegionDebugString for RegionPrettyPrinter<'_, '_> {
    fn override_region_debug_string(&self, region: RegionVid) -> Option<&str> {
        self.region_to_string.get(&region).map(|s| s.as_str())
    }
}

impl<'bc, 'tcx> RegionPrettyPrinter<'bc, 'tcx> {
    pub(crate) fn new(region_infer_ctxt: &'bc RegionInferenceContext<'tcx>) -> Self {
        RegionPrettyPrinter {
            region_to_string: BTreeMap::new(),
            sccs: RefCell::new(None),
            region_infer_ctxt,
        }
    }

    pub fn insert(&mut self, region: RegionVid, string: String) {
        assert!(self.region_to_string.insert(region, string).is_none());
        self.sccs.borrow_mut().take();
    }

    #[allow(dead_code)]
    pub(crate) fn lookup(&self, region: RegionVid) -> Option<&String> {
        if self.sccs.borrow().is_none() {
            let regions = self.region_to_string.keys().copied().collect::<Vec<_>>();
            *self.sccs.borrow_mut() = Some(compute_region_sccs(&regions, self.region_infer_ctxt));
        }
        for scc in self.sccs.borrow().as_ref().unwrap().node_weights() {
            if scc.contains(&region) {
                for r in scc {
                    if let Some(s) = self.region_to_string.get(r) {
                        return Some(s);
                    }
                }
            }
        }
        None
    }
}

fn get_all_regions<'tcx>(body: &Body<'tcx>, _tcx: ty::TyCtxt<'tcx>) -> Vec<RegionVid> {
    body.local_decls
        .iter()
        .flat_map(|l| extract_regions(l.ty))
        .filter_map(|r| r.vid())
        .unique()
        .collect()
}

fn compute_region_sccs(
    regions: &[RegionVid],
    region_infer_ctxt: &RegionInferenceContext<'_>,
) -> petgraph::Graph<Vec<RegionVid>, ()> {
    let mut graph = petgraph::Graph::new();
    let indices: BTreeMap<RegionVid, NodeIndex> = regions
        .iter()
        .copied()
        .map(|r| (r, graph.add_node(r)))
        .collect::<BTreeMap<_, _>>();
    for r1 in regions {
        for r2 in regions {
            if r1 != r2 && region_infer_ctxt.eval_outlives(*r1, *r2) {
                graph.add_edge(indices[r1], indices[r2], ());
            }
        }
    }
    let mut scc_graph = petgraph::algo::condensation(graph, true);
    let toposort = petgraph::algo::toposort(&scc_graph, None).unwrap();
    let (g, revmap) = petgraph::algo::tred::dag_to_toposorted_adjacency_list(&scc_graph, &toposort);
    let (reduced, _) = petgraph::algo::tred::dag_transitive_reduction_closure::<_, u32>(&g);
    scc_graph.retain_edges(|slf, ei| {
        let endpoints = slf.edge_endpoints(ei).unwrap();
        reduced.contains_edge(revmap[endpoints.0.index()], revmap[endpoints.1.index()])
    });
    scc_graph
}

#[must_use]
pub fn region_inference_outlives<'a, 'tcx: 'a, 'bc>(
    ctxt: CompilerCtxt<'a, 'tcx, &'bc RustBorrowCheckerImpl<'a, 'tcx>>,
) -> String {
    let regions = get_all_regions(ctxt.body(), ctxt.tcx());
    let scc_graph = compute_region_sccs(&regions, ctxt.borrow_checker.region_infer_ctxt());
    let scc_graph = scc_graph.map(
        |_, regions| {
            format!(
                "[{}]",
                regions
                    .iter()
                    .map(|r| r.display_string(ctxt))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        },
        |_, ()| "",
    );
    petgraph::dot::Dot::new(&scc_graph).to_string()
}

#[must_use]
pub fn subset_at_location<'a, 'tcx: 'a, 'bc>(
    location: Location,
    start: bool,
    ctxt: CompilerCtxt<'a, 'tcx, &'bc PoloniusBorrowChecker<'a, 'tcx>>,
) -> DotGraph {
    let mut graph = DotGraph {
        nodes: vec![],
        edges: vec![],
        name: "bcfacts".into(),
    };
    let mut nodes = IdLookup::new('n');
    let location_index = if start {
        ctxt.borrow_checker.location_table().start_index(location)
    } else {
        ctxt.borrow_checker.location_table().mid_index(location)
    };
    if let Some(subset) = ctxt.borrow_checker.output_facts.subset.get(&location_index) {
        for (sup, subs) in subset {
            let sup_node = get_id(sup, &mut nodes, &mut graph.nodes, ctxt);
            for sub in subs {
                let sub_node = get_id(sub, &mut nodes, &mut graph.nodes, ctxt);
                graph.edges.push(DotEdge {
                    id: None,
                    from: sup_node.clone(),
                    to: sub_node.clone(),
                    options: EdgeOptions::directed(EdgeDirection::Forward),
                });
            }
        }
    }
    graph
}
