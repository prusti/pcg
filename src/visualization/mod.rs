//! Logic for generating debug visualizations of the PCG
// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

pub mod bc_facts_graph;
pub(crate) mod ctxt;
pub mod dot_graph;
pub mod drawer;
pub(crate) mod functions_metadata;
pub mod graph_constructor;
mod grapher;
pub mod legend;
pub mod mir_graph;
mod node;
mod settings;
mod svg_graph;
pub(crate) use functions_metadata::*;
use std::borrow::Cow;
pub(crate) mod stmt_graphs;

#[cfg(feature = "type-export")]
pub use mir_graph::SourcePos;

use crate::{
    borrow_pcg::{
        edge::borrow_flow::BorrowFlowEdgeKind, graph::BorrowsGraph, unblock_graph::UnblockGraph,
        validity_conditions::ValidityConditions,
    },
    pcg::{CapabilityKind, PcgRef, place_capabilities::PlaceCapabilitiesReader},
    rustc_interface::middle::mir::Location,
    utils::{
        CompilerCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, Place, SnapshotLocation,
        display::{DisplayWithCtxt, OutputMode},
        html::Html,
    },
    visualization::{dot_graph::DotEdgeId, drawer::GraphDrawer},
};
use std::{
    collections::HashSet,
    fs::File,
    io::{self},
    path::Path,
};

use graph_constructor::BorrowsGraphConstructor;

use self::{
    dot_graph::{
        DotEdge, DotFloatAttr, DotLabel, DotNode, DotStringAttr, EdgeDirection, EdgeOptions,
    },
    graph_constructor::PcgGraphConstructor,
};

#[must_use]
pub fn place_id(place: &Place<'_>) -> String {
    format!("{place:?}")
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct NodeId(char, usize);

impl std::fmt::Display for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", self.0, self.1)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct GraphNode {
    id: NodeId,
    node_type: NodeType,
}

impl GraphNode {
    pub(crate) fn label_text(&self) -> Cow<'_, str> {
        match &self.node_type {
            NodeType::PlaceNode { label, .. } => label.into(),
            NodeType::RegionProjectionNode { label, .. } => label.text(),
        }
    }

    fn to_dot_node(&self) -> DotNode {
        match &self.node_type {
            NodeType::PlaceNode {
                owned,
                capability,
                location,
                label,
                ty,
            } => {
                let location_html: Html = match location {
                    Some(l) => Html::Seq(vec![
                        Html::space(),
                        l.display_output((), OutputMode::Short).into_html(),
                    ]),
                    None => Html::empty(),
                };
                let color = if location.is_some()
                    || matches!(capability, None | Some(CapabilityKind::Write))
                {
                    "gray"
                } else if *owned {
                    "black"
                } else {
                    "darkgreen"
                };
                let (style, penwidth) = if *owned {
                    (None, None)
                } else {
                    (
                        Some(DotStringAttr("rounded".into())),
                        Some(DotFloatAttr(1.5)),
                    )
                };
                let capability_text = match capability {
                    Some(k) => format!(": {k:?}"),
                    None => String::new(),
                };
                let label_html = Html::Font(
                    "courier",
                    Box::new(Html::Seq(vec![
                        Html::Text(format!("{label}{capability_text}").into()),
                        location_html,
                    ])),
                );
                DotNode {
                    id: self.id.to_string(),
                    label: DotLabel::Html(label_html),
                    color: DotStringAttr(color.into()),
                    font_color: DotStringAttr(color.into()),
                    shape: DotStringAttr("rect".into()),
                    style,
                    penwidth,
                    tooltip: Some(DotStringAttr(ty.clone().into())),
                }
            }
            NodeType::RegionProjectionNode {
                label,
                loans,
                base_ty: place_ty,
            } => DotNode {
                id: self.id.to_string(),
                label: DotLabel::Html(label.clone()),
                color: DotStringAttr("blue".into()),
                font_color: DotStringAttr("blue".into()),
                shape: DotStringAttr("octagon".into()),
                style: None,
                penwidth: None,
                tooltip: Some(DotStringAttr(format!("{place_ty}\\\n{loans}").into())),
            },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum NodeType {
    PlaceNode {
        owned: bool,
        label: String,
        capability: Option<CapabilityKind>,
        location: Option<SnapshotLocation>,
        ty: String,
    },
    RegionProjectionNode {
        label: Html,
        base_ty: String,
        loans: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) enum ExpansionKind {
    Deref,
    Unpack,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum GraphEdge<'a> {
    Abstract {
        blocked: NodeId,
        blocking: NodeId,
        label: String,
    },
    // For literal borrows
    Alias {
        blocked_place: NodeId,
        blocking_place: NodeId,
    },
    Borrow {
        borrowed_place: NodeId,
        assigned_region_projection: NodeId,
        kind: String,
        location: Location,
        region: String,
        validity_conditions: &'a ValidityConditions,
        borrow_index: Option<String>,
    },
    Projection {
        source: NodeId,
        target: NodeId,
    },
    DerefExpansion {
        sources: Vec<NodeId>,
        targets: Vec<NodeId>,
        kind: ExpansionKind,
        validity_conditions: &'a ValidityConditions,
    },
    BorrowFlow {
        source: NodeId,
        target: NodeId,
        kind: BorrowFlowEdgeKind<'a, String>,
    },
    Coupled {
        sources: Vec<NodeId>,
        targets: Vec<NodeId>,
    },
    Delegation {
        source: NodeId,
        target: NodeId,
    },
    RawPtrDeref {
        source: NodeId,
        target: NodeId,
    },
}

impl<'a> GraphEdge<'a> {
    fn label_text(&self) -> String {
        match self {
            Self::Abstract { label, .. } => label.clone(),
            Self::Borrow {
                kind,
                region,
                borrow_index,
                ..
            } => format!(
                "{}{} {}",
                borrow_index
                    .as_ref()
                    .map_or_else(String::new, |index| format!("{index}: ")),
                kind,
                region
            ),
            Self::BorrowFlow { kind, .. } => kind.to_string(),
            Self::Alias { .. }
            | Self::Projection { .. }
            | Self::DerefExpansion { .. }
            | Self::Coupled { .. }
            | Self::Delegation { .. }
            | Self::RawPtrDeref { .. } => String::new(),
        }
    }

    fn endpoints(&self) -> (Vec<NodeId>, Vec<NodeId>) {
        match self {
            Self::DerefExpansion {
                sources, targets, ..
            }
            | Self::Coupled { sources, targets } => (sources.clone(), targets.clone()),
            Self::Abstract {
                blocked, blocking, ..
            } => (vec![*blocked], vec![*blocking]),
            Self::Alias {
                blocked_place,
                blocking_place,
            } => (vec![*blocked_place], vec![*blocking_place]),
            Self::Borrow {
                borrowed_place,
                assigned_region_projection,
                ..
            } => (vec![*borrowed_place], vec![*assigned_region_projection]),
            Self::Projection { source, target }
            | Self::BorrowFlow { source, target, .. }
            | Self::Delegation { source, target }
            | Self::RawPtrDeref { source, target } => (vec![*source], vec![*target]),
        }
    }

    fn to_dot_edges<'tcx: 'a>(&self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> Vec<DotEdge> {
        let (sources, targets) = self.endpoints();
        sources
            .into_iter()
            .flat_map(|source| {
                targets
                    .iter()
                    .map(move |&target| self.to_dot_edge(None, source, target, ctxt))
            })
            .collect()
    }

    pub(crate) fn validity_conditions(&self) -> Option<&'a ValidityConditions> {
        match self {
            GraphEdge::Borrow {
                validity_conditions,
                ..
            }
            | GraphEdge::DerefExpansion {
                validity_conditions,
                ..
            } => Some(validity_conditions),
            GraphEdge::Projection { .. }
            | GraphEdge::Alias { .. }
            | GraphEdge::Abstract { .. }
            | GraphEdge::BorrowFlow { .. }
            | GraphEdge::Coupled { .. }
            | GraphEdge::Delegation { .. }
            | GraphEdge::RawPtrDeref { .. } => None,
        }
    }
    pub(super) fn to_dot_edge<'tcx: 'a>(
        &self,
        edge_id: Option<DotEdgeId>,
        source: NodeId,
        target: NodeId,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> DotEdge {
        match self {
            GraphEdge::Projection { source, target } => DotEdge {
                id: edge_id,
                from: source.to_string(),
                to: target.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Forward),
            },
            GraphEdge::Alias {
                blocked_place,
                blocking_place,
            } => DotEdge {
                id: edge_id,
                from: blocked_place.to_string(),
                to: blocking_place.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Forward)
                    .with_color("grey".into())
                    .with_style("dashed"),
            },
            GraphEdge::Borrow {
                borrowed_place,
                assigned_region_projection: assigned_place,
                validity_conditions,
                ..
            } => DotEdge {
                id: edge_id,
                to: assigned_place.to_string(),
                from: borrowed_place.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Forward)
                    .with_color("orange".into())
                    .with_label(self.label_text())
                    .with_tooltip(
                        validity_conditions
                            .display_output(ctxt, OutputMode::Short)
                            .into_text(),
                    ),
            },
            GraphEdge::DerefExpansion {
                validity_conditions,
                ..
            } => DotEdge {
                id: edge_id,
                from: source.to_string(),
                to: target.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Forward)
                    .with_color("green".into())
                    .with_tooltip(
                        validity_conditions
                            .display_output(ctxt, OutputMode::Short)
                            .into_text(),
                    ),
            },
            GraphEdge::Abstract {
                blocked, blocking, ..
            } => DotEdge {
                id: edge_id,
                from: blocked.to_string(),
                to: blocking.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Forward)
                    .with_label(self.label_text())
                    .with_penwidth(3.0),
            },
            GraphEdge::BorrowFlow {
                source,
                target,
                kind,
            } => {
                let options = EdgeOptions::directed(EdgeDirection::Forward)
                    .with_label(self.label_text())
                    .with_color("purple".into());
                let options = match kind {
                    BorrowFlowEdgeKind::BorrowOutlives { regions_equal } => {
                        if *regions_equal {
                            options.with_penwidth(2.0)
                        } else {
                            options.with_style("dashed")
                        }
                    }
                    _ => options,
                };
                DotEdge {
                    id: edge_id,
                    from: source.to_string(),
                    to: target.to_string(),
                    options,
                }
            }
            GraphEdge::Coupled { .. } => DotEdge {
                id: edge_id,
                from: source.to_string(),
                to: target.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Forward)
                    .with_color("red".into())
                    .with_style("dashed"),
            },
            GraphEdge::Delegation { source, target } => DotEdge {
                id: edge_id,
                from: source.to_string(),
                to: target.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Forward)
                    .with_color("blue".into())
                    .with_style("dashed"),
            },
            GraphEdge::RawPtrDeref { source, target } => DotEdge {
                id: edge_id,
                from: source.to_string(),
                to: target.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Forward)
                    .with_color("green".into())
                    .with_style("dashed"),
            },
        }
    }
}

pub struct Graph<'a> {
    nodes: Vec<GraphNode>,
    edges: HashSet<GraphEdge<'a>>,
}

impl<'a> Graph<'a> {
    fn new(nodes: Vec<GraphNode>, edges: HashSet<GraphEdge<'a>>) -> Self {
        Self { nodes, edges }
    }

    pub fn has_edge_between_labelled_nodes<'tcx: 'a>(
        &self,
        label1: &str,
        label2: &str,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> bool {
        let Some(label_1_id) = self
            .nodes
            .iter()
            .find(|n| n.label_text() == label1)
            .map(|n| n.id)
        else {
            return false;
        };
        let Some(label_2_id) = self
            .nodes
            .iter()
            .find(|n| n.label_text() == label2)
            .map(|n| n.id)
        else {
            return false;
        };
        self.edges.iter().any(|edge| {
            edge.to_dot_edges(ctxt).iter().any(|dot_edge| {
                dot_edge.from == label_1_id.to_string() && dot_edge.to == label_2_id.to_string()
            })
        })
    }
}

pub(crate) fn generate_borrows_dot_graph<'a, 'tcx: 'a>(
    ctxt: CompilerCtxt<'a, 'tcx>,
    capabilities: &impl PlaceCapabilitiesReader<'tcx>,
    borrows_domain: &'a BorrowsGraph<'tcx>,
) -> io::Result<String> {
    let constructor = BorrowsGraphConstructor::new(borrows_domain, capabilities, ctxt.bc_ctxt());
    let graph = constructor.construct_graph();
    let mut buf = vec![];
    let drawer = GraphDrawer::new(&mut buf, None);
    drawer.draw(&graph, ctxt)?;
    Ok(String::from_utf8(buf).unwrap())
}

pub(crate) fn generate_unblock_dot_graph<'a, 'tcx: 'a>(
    ctxt: CompilerCtxt<'a, 'tcx>,
    capabilities: &impl PlaceCapabilitiesReader<'tcx>,
    unblock_graph: &UnblockGraph<'tcx>,
) -> io::Result<String> {
    let mut borrows_graph = BorrowsGraph::default();
    for edge in unblock_graph.edges() {
        borrows_graph.insert(edge.clone(), ctxt.bc_ctxt());
    }
    let constructor = BorrowsGraphConstructor::new(&borrows_graph, capabilities, ctxt.bc_ctxt());
    let graph = constructor.construct_graph();
    let mut buf = vec![];
    let drawer = GraphDrawer::new(&mut buf, None);
    drawer.draw(&graph, ctxt)?;
    Ok(String::from_utf8(buf).unwrap())
}

pub(crate) fn generate_pcg_dot_graph<'a, 'tcx: 'a>(
    pcg: PcgRef<'a, 'tcx>,
    ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    location: Location,
) -> io::Result<String> {
    let constructor = PcgGraphConstructor::new(pcg, ctxt.bc_ctxt(), location);
    let graph = constructor.construct_graph();
    let mut buf = vec![];
    let drawer = GraphDrawer::new(&mut buf, None);
    drawer.draw(&graph, ctxt)?;
    Ok(String::from_utf8(buf).unwrap())
}

pub(crate) fn write_pcg_graph_to_file<'a, 'tcx: 'a>(
    pcg: PcgRef<'a, 'tcx>,
    ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    location: Location,
    file_path: &Path,
    legacy_graph_renderer: bool,
) -> io::Result<()> {
    let constructor = PcgGraphConstructor::new(pcg, ctxt.bc_ctxt(), location);
    let graph = constructor.construct_graph();
    let dot_file = File::create(file_path).unwrap();
    let ctxt_file = File::create(file_path.with_extension("json")).unwrap();
    let drawer = GraphDrawer::new(dot_file, Some(ctxt_file));
    drawer.draw(&graph, ctxt)?;
    if legacy_graph_renderer {
        for extension in ["svg", "svg.json", "hypergraph.json"] {
            match std::fs::remove_file(file_path.with_extension(extension)) {
                Ok(()) => {}
                Err(error) if error.kind() == io::ErrorKind::NotFound => {}
                Err(error) => return Err(error),
            }
        }
        Ok(())
    } else {
        graph.write_svg(file_path, ctxt)
    }
}
