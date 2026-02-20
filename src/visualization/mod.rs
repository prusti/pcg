//! Logic for generating debug visualizations of the PCG
// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

pub mod bc_facts_graph;
pub(crate) mod ctxt;
pub(crate) mod data;
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
        edge::borrow_flow::BorrowFlowEdgeKind, graph::BorrowsGraph,
        validity_conditions::ValidityConditions,
    },
    pcg::{
        PcgRef, PositiveCapability, SymbolicCapability, place_capabilities::PlaceCapabilitiesReader,
    },
    rustc_interface::middle::mir::Location,
    utils::{
        DebugCtxt, HasBorrowCheckerCtxt, HasCompilerCtxt, Place, SnapshotLocation,
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
                    || capability.is_none()
                    || matches!(capability, Some(PositiveCapability::Write))
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
        capability: Option<PositiveCapability>,
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
        source: NodeId,
        target: NodeId,
        validity_conditions: &'a ValidityConditions,
    },
    BorrowFlow {
        source: NodeId,
        target: NodeId,
        kind: BorrowFlowEdgeKind<'a, String>,
    },
    Coupled {
        source: NodeId,
        target: NodeId,
    },
}

impl<'a> GraphEdge<'a> {
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
            | GraphEdge::Coupled { .. } => None,
        }
    }
    pub(super) fn to_dot_edge<'mir: 'a, 'tcx: 'mir>(
        &self,
        edge_id: Option<DotEdgeId>,
        ctxt: impl HasCompilerCtxt<'mir, 'tcx>,
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
                            String::new()
                        },
                        kind,
                        region
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
            GraphEdge::Coupled { source, target } => DotEdge {
                id: edge_id,
                from: source.to_string(),
                to: target.to_string(),
                options: EdgeOptions::directed(EdgeDirection::Forward)
                    .with_color("red".into())
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
            let dot_edge = edge.to_dot_edge(None, ctxt);
            dot_edge.from == label_1_id.to_string() && dot_edge.to == label_2_id.to_string()
        })
    }
}

pub(crate) fn generate_pcg_dot_graph<'pcg, 'a: 'pcg, 'tcx: 'a>(
    pcg: PcgRef<'pcg, 'tcx>,
    ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    location: Option<Location>,
) -> io::Result<String> {
    let constructor = PcgGraphConstructor::new(pcg, ctxt.bc_ctxt(), location);
    let graph = constructor.construct_graph();
    let mut buf = vec![];
    let drawer = GraphDrawer::new(&mut buf, None);
    drawer.draw(&graph, ctxt)?;
    Ok(String::from_utf8(buf).unwrap())
}

pub(crate) fn write_pcg_dot_graph_to_file<'a, 'tcx: 'a>(
    pcg: PcgRef<'a, 'tcx>,
    ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    location: Location,
    file_path: &Path,
) -> io::Result<()> {
    let constructor = PcgGraphConstructor::new(pcg, ctxt.bc_ctxt(), Some(location));
    let graph = constructor.construct_graph();
    let dot_file = File::create(file_path).unwrap();
    let ctxt_file = File::create(file_path.with_extension("json")).unwrap();
    let drawer = GraphDrawer::new(dot_file, Some(ctxt_file));
    drawer.draw(&graph, ctxt)
}
