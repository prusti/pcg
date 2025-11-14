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
pub(crate) use functions_metadata::*;
use std::borrow::Cow;
pub(crate) mod stmt_graphs;

#[cfg(feature = "type-export")]
pub use mir_graph::SourcePos;

use crate::{
    borrow_pcg::{
        edge::outlives::BorrowFlowEdgeKind, graph::BorrowsGraph,
        validity_conditions::ValidityConditions,
    },
    pcg::{
        CapabilityKind, PcgRef, SymbolicCapability, place_capabilities::PlaceCapabilitiesReader,
    },
    rustc_interface::middle::mir::Location,
    utils::{
        HasBorrowCheckerCtxt, HasCompilerCtxt, Place, SnapshotLocation,
        display::{DisplayWithCtxt, OutputMode},
        html::Html,
    },
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

pub fn place_id(place: &Place<'_>) -> String {
    format!("{place:?}")
}

pub struct GraphDrawer<T: io::Write> {
    out: T,
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
                    || capability.is_none()
                    || matches!(capability, Some(CapabilityKind::Write))
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
                        Some(DotStringAttr("rounded".to_string())),
                        Some(DotFloatAttr(1.5)),
                    )
                };
                let capability_text = match capability {
                    Some(k) => format!(": {k:?}"),
                    None => "".to_string(),
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
                    color: DotStringAttr(color.to_string()),
                    font_color: DotStringAttr(color.to_string()),
                    shape: DotStringAttr("rect".to_string()),
                    style,
                    penwidth,
                    tooltip: Some(DotStringAttr(ty.clone())),
                }
            }
            NodeType::RegionProjectionNode {
                label,
                loans,
                base_ty: place_ty,
            } => DotNode {
                id: self.id.to_string(),
                label: DotLabel::Html(label.clone()),
                color: DotStringAttr("blue".to_string()),
                font_color: DotStringAttr("blue".to_string()),
                shape: DotStringAttr("octagon".to_string()),
                style: None,
                penwidth: None,
                tooltip: Some(DotStringAttr(format!("{place_ty}\\\n{loans}"))),
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
        location: Option<Location>,
        region: Option<String>,
        validity_conditions: &'a ValidityConditions,
        borrow_index: Option<String>,
    },
    Projection {
        source: NodeId,
        target: NodeId,
    },
    DerefExpansion {
        source: NodeId,
        target: NodeId,
        validity_conditions: &'a ValidityConditions,
    },
    BorrowFlow {
        source: NodeId,
        target: NodeId,
        kind: BorrowFlowEdgeKind,
    },
    Coupled {
        source: NodeId,
        target: NodeId,
    },
}

impl<'a> GraphEdge<'a> {
    pub(super) fn to_dot_edge<'tcx: 'a>(
        &self,
        edge_id: Option<usize>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> DotEdge {
        let edge_id = edge_id.map(|id| format!("edge_{id}"));
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
                    .with_style("dashed".to_string()),
            },
            GraphEdge::Borrow {
                borrowed_place,
                assigned_region_projection: assigned_place,
                location: _,
                region,
                kind,
                validity_conditions,
                borrow_index,
            } => DotEdge {
                id: edge_id,
                to: assigned_place.to_string(),
                from: borrowed_place.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Forward)
                    .with_color("orange".into())
                    .with_label(format!(
                        "{}{} {}",
                        if let Some(borrow_index) = borrow_index {
                            format!("{borrow_index}: ")
                        } else {
                            "".to_string()
                        },
                        kind,
                        region.as_ref().cloned().unwrap_or("".to_string())
                    ))
                    .with_tooltip(
                        validity_conditions
                            .display_output(ctxt, OutputMode::Short)
                            .into_text(),
                    ),
            },
            GraphEdge::DerefExpansion {
                source,
                target,
                validity_conditions,
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
                blocked,
                blocking,
                label,
            } => DotEdge {
                id: edge_id,
                from: blocked.to_string(),
                to: blocking.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Forward)
                    .with_label(label.clone())
                    .with_penwidth(3.0),
            },
            GraphEdge::BorrowFlow {
                source,
                target,
                kind,
            } => {
                let options = EdgeOptions::directed(EdgeDirection::Forward)
                    .with_label(format!("{kind}"))
                    .with_color("purple".into());
                let options = match kind {
                    BorrowFlowEdgeKind::BorrowOutlives { regions_equal } => {
                        if *regions_equal {
                            options.with_penwidth(2.0)
                        } else {
                            options.with_style("dashed".to_string())
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
            GraphEdge::Coupled { source, target } => DotEdge {
                id: edge_id,
                from: source.to_string(),
                to: target.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Forward)
                    .with_color("red".into())
                    .with_style("dashed".to_string()),
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
            let dot_edge = edge.to_dot_edge(None, ctxt);
            dot_edge.from == label_1_id.to_string() && dot_edge.to == label_2_id.to_string()
        })
    }
}

pub(crate) fn generate_borrows_dot_graph<'a, 'tcx: 'a>(
    ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    capabilities: &'a impl PlaceCapabilitiesReader<'tcx, SymbolicCapability>,
    borrows_domain: &'a BorrowsGraph<'tcx>,
) -> io::Result<String> {
    let constructor = BorrowsGraphConstructor::new(borrows_domain, capabilities, ctxt.bc_ctxt());
    let graph = constructor.construct_graph();
    let mut buf = vec![];
    let drawer = GraphDrawer::new(&mut buf);
    drawer.draw(graph, ctxt)?;
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
    let drawer = GraphDrawer::new(&mut buf);
    drawer.draw(graph, ctxt)?;
    Ok(String::from_utf8(buf).unwrap())
}

pub(crate) fn write_pcg_dot_graph_to_file<'a, 'tcx: 'a>(
    pcg: PcgRef<'a, 'tcx>,
    ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    location: Location,
    file_path: &Path,
) -> io::Result<()> {
    let constructor = PcgGraphConstructor::new(pcg, ctxt.bc_ctxt(), location);
    let graph = constructor.construct_graph();
    let drawer = GraphDrawer::new(File::create(file_path).unwrap_or_else(|e| {
        panic!("Failed to create file at path: {file_path:?}: {e}");
    }));
    drawer.draw(graph, ctxt)
}
