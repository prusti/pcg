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
pub(crate) mod html;

#[cfg(feature = "type-export")]
pub use mir_graph::SourcePos;

use crate::{
    borrow_pcg::{edge::outlives::BorrowFlowEdgeKind, graph::BorrowsGraph},
    pcg::{
        CapabilityKind, PcgRef, SymbolicCapability, place_capabilities::PlaceCapabilitiesReader,
    },
    rustc_interface::middle::mir::Location,
    utils::{
        HasBorrowCheckerCtxt, Place, SnapshotLocation,
        display::DisplayWithCtxt,
    },
    visualization::html::Html,
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
    pub(crate) fn label_text(&self) -> String {
        match &self.node_type {
            NodeType::PlaceNode { label, .. } => label.clone(),
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
                let capability_text = match capability {
                    Some(k) => format!("{k:?}"),
                    None => "".to_string(),
                };
                let location_html: Html = match location {
                    Some(l) => Html::Seq(vec![
                        " at ".into(),
                        l.display_html(()),
                    ]),
                    None => Html::Text(String::new()),
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
                let label_html = Html::Font(
                    "courier",
                    Box::new(Html::Seq(vec![
                        Html::Text(label.clone()),
                        Html::Text(": ".to_string()),
                        capability_text.into(),
                        location_html
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
pub(crate) enum GraphEdge {
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
        path_conditions: String,
        borrow_index: Option<String>,
    },
    Projection {
        source: NodeId,
        target: NodeId,
    },
    DerefExpansion {
        source: NodeId,
        target: NodeId,
        path_conditions: String,
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

impl GraphEdge {
    pub(super) fn to_dot_edge(&self) -> DotEdge {
        match self {
            GraphEdge::Projection { source, target } => DotEdge {
                from: source.to_string(),
                to: target.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Forward),
            },
            GraphEdge::Alias {
                blocked_place,
                blocking_place,
            } => DotEdge {
                from: blocked_place.to_string(),
                to: blocking_place.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Forward)
                    .with_color("grey".to_string())
                    .with_style("dashed".to_string()),
            },
            GraphEdge::Borrow {
                borrowed_place,
                assigned_region_projection: assigned_place,
                location: _,
                region,
                kind,
                path_conditions,
                borrow_index,
            } => DotEdge {
                to: assigned_place.to_string(),
                from: borrowed_place.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Forward)
                    .with_color("orange".to_string())
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
                    .with_tooltip(path_conditions.clone()),
            },
            GraphEdge::DerefExpansion {
                source,
                target,
                path_conditions,
            } => DotEdge {
                from: source.to_string(),
                to: target.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Forward)
                    .with_color("green".to_string())
                    .with_tooltip(path_conditions.clone()),
            },
            GraphEdge::Abstract {
                blocked,
                blocking,
                label,
            } => DotEdge {
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
                    .with_color("purple".to_string());
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
                    from: source.to_string(),
                    to: target.to_string(),
                    options,
                }
            }
            GraphEdge::Coupled { source, target } => DotEdge {
                from: source.to_string(),
                to: target.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Forward)
                    .with_color("red".to_string())
                    .with_style("dashed".to_string()),
            },
        }
    }
}

pub struct Graph {
    nodes: Vec<GraphNode>,
    edges: HashSet<GraphEdge>,
}

impl Graph {
    fn new(nodes: Vec<GraphNode>, edges: HashSet<GraphEdge>) -> Self {
        Self { nodes, edges }
    }

    pub fn has_edge_between_labelled_nodes(&self, label1: &str, label2: &str) -> bool {
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
            let dot_edge = edge.to_dot_edge();
            dot_edge.from == label_1_id.to_string() && dot_edge.to == label_2_id.to_string()
        })
    }
}

pub(crate) fn generate_borrows_dot_graph<'a, 'tcx: 'a, 'bc>(
    ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    capabilities: &impl PlaceCapabilitiesReader<'tcx, SymbolicCapability>,
    borrows_domain: &BorrowsGraph<'tcx>,
) -> io::Result<String> {
    let constructor = BorrowsGraphConstructor::new(borrows_domain, capabilities, ctxt.bc_ctxt());
    let graph = constructor.construct_graph();
    let mut buf = vec![];
    let drawer = GraphDrawer::new(&mut buf);
    drawer.draw(graph)?;
    Ok(String::from_utf8(buf).unwrap())
}

pub(crate) fn generate_pcg_dot_graph<'pcg, 'a: 'pcg, 'tcx: 'a>(
    pcg: PcgRef<'pcg, 'tcx>,
    ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    location: Location,
) -> io::Result<String> {
    let constructor = PcgGraphConstructor::new(pcg, ctxt.bc_ctxt(), location);
    let graph = constructor.construct_graph();
    let mut buf = vec![];
    let drawer = GraphDrawer::new(&mut buf);
    drawer.draw(graph)?;
    Ok(String::from_utf8(buf).unwrap())
}

pub(crate) fn write_pcg_dot_graph_to_file<'a, 'tcx: 'a>(
    pcg: PcgRef<'_, 'tcx>,
    ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    location: Location,
    file_path: &Path,
) -> io::Result<()> {
    let constructor = PcgGraphConstructor::new(pcg, ctxt.bc_ctxt(), location);
    let graph = constructor.construct_graph();
    let drawer = GraphDrawer::new(File::create(file_path).unwrap_or_else(|e| {
        panic!("Failed to create file at path: {file_path:?}: {e}");
    }));
    drawer.draw(graph)
}
