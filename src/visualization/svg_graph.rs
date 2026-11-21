use std::{collections::BTreeMap, fs, io, path::Path};

use pcg_svg::{Color, Hyperedge, Hypergraph, Node, Shape};

use crate::{
    borrow_pcg::{
        edge::borrow_flow::BorrowFlowEdgeKind,
        validity_conditions::{ValidityConditions, ValidityConditionsDebugRepr},
    },
    pcg::CapabilityKind,
    utils::{
        DebugRepr, HasCompilerCtxt,
        display::{DisplayWithCtxt, OutputMode},
    },
};

use super::{ExpansionKind, Graph, GraphEdge, NodeId, NodeType};

impl Graph<'_> {
    /// Converts the visualization graph without splitting its hyperedges.
    pub fn to_hypergraph<'a, 'tcx: 'a>(&self, ctxt: impl HasCompilerCtxt<'a, 'tcx>) -> Hypergraph {
        self.svg_data(ctxt).0
    }

    pub(super) fn write_svg<'a, 'tcx: 'a>(
        &self,
        dot_path: &Path,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> io::Result<()> {
        let (graph, metadata) = self.svg_data(ctxt);
        let svg = graph.to_svg().map_err(io::Error::other)?;
        fs::write(dot_path.with_extension("svg"), svg)?;
        serde_json::to_writer_pretty(
            fs::File::create(dot_path.with_extension("svg.json"))?,
            &metadata,
        )?;
        serde_json::to_writer_pretty(
            fs::File::create(dot_path.with_extension("hypergraph.json"))?,
            &graph,
        )?;
        Ok(())
    }

    fn svg_data<'a, 'tcx: 'a>(
        &self,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> (Hypergraph, BTreeMap<String, ValidityConditionsDebugRepr>) {
        let mut graph = Hypergraph::default();
        let mut ids = BTreeMap::new();
        let mut nodes: Vec<_> = self.nodes.iter().collect();
        // Labels and types determine order independently of hash iteration during analysis.
        nodes.sort_by_key(|n| (n.label_text().into_owned(), format!("{:?}", n.node_type)));
        for node in nodes {
            let native = match &node.node_type {
                NodeType::PlaceNode {
                    owned,
                    label,
                    capability,
                    location,
                    ty,
                } => {
                    let label = if let Some(location) = location {
                        format!(
                            "{label} {}",
                            location.display_output((), OutputMode::Short).into_text()
                        )
                    } else {
                        label.clone()
                    };
                    Node {
                        label,
                        suffix: capability.map(|c| format!("{c:?}")),
                        tooltip: ty.clone(),
                        color: if location.is_some()
                            || matches!(capability, None | Some(CapabilityKind::Write))
                        {
                            Color::Gray
                        } else if *owned {
                            Color::Black
                        } else {
                            Color::Green
                        },
                        shape: if *owned {
                            Shape::Rectangle
                        } else {
                            Shape::Rounded
                        },
                    }
                }
                NodeType::RegionProjectionNode {
                    label,
                    base_ty,
                    loans,
                } => Node {
                    label: label.text().into_owned(),
                    suffix: None,
                    tooltip: format!("{base_ty}\n{loans}"),
                    color: Color::Blue,
                    shape: Shape::Octagon,
                },
            };
            ids.insert(node.id, graph.add_node(native));
        }
        let mut converted = Vec::<(Hyperedge, Option<&ValidityConditions>)>::new();
        let mut projections = BTreeMap::<NodeId, Vec<NodeId>>::new();
        for edge in &self.edges {
            if let GraphEdge::Projection { source, target } = edge {
                projections.entry(*source).or_default().push(*target);
                continue;
            }
            let (sources, targets) = edge.endpoints();
            // An expansion of a zero-field value has no drawable relation.
            if sources.is_empty() || targets.is_empty() {
                continue;
            }
            let mut native = Hyperedge::new(
                sources.iter().map(|n| ids[n]).collect(),
                targets.iter().map(|n| ids[n]).collect(),
                edge.label_text(),
            );
            match edge {
                GraphEdge::Abstract { .. } => {
                    native.thick = true;
                }
                GraphEdge::Alias { .. } => {
                    native.color = Color::Gray;
                    native.dashed = true;
                }
                GraphEdge::Borrow { borrow_index, .. } => {
                    native.color = Color::Orange;
                    if let Some(index) = borrow_index {
                        native.tooltip.clone_from(index);
                    }
                }
                GraphEdge::DerefExpansion { kind, .. } => match kind {
                    ExpansionKind::Deref => {
                        native.color = Color::Green;
                    }
                    ExpansionKind::Unpack => {}
                },
                GraphEdge::BorrowFlow { kind, .. } => {
                    native.color = Color::Purple;
                    if let BorrowFlowEdgeKind::BorrowOutlives { regions_equal } = kind {
                        native.thick = *regions_equal;
                        native.dashed = !regions_equal;
                    }
                }
                GraphEdge::Coupled { .. } => {
                    native.color = Color::Red;
                    native.dashed = true;
                }
                GraphEdge::Delegation { .. } => {
                    native.color = Color::Blue;
                    native.dashed = true;
                }
                GraphEdge::RawPtrDeref { .. } => {
                    native.color = Color::Green;
                    native.dashed = true;
                }
                GraphEdge::Projection { .. } => unreachable!(),
            }
            if let Some(conditions) = edge.validity_conditions() {
                if !native.tooltip.is_empty() {
                    native.tooltip.push('\n');
                }
                native.tooltip.push_str(
                    &conditions
                        .display_output(ctxt, OutputMode::Short)
                        .into_text(),
                );
            }
            converted.push((native, edge.validity_conditions()));
        }
        for (source, targets) in projections {
            converted.push((
                Hyperedge::new(
                    vec![ids[&source]],
                    targets.iter().map(|n| ids[n]).collect(),
                    "",
                ),
                None,
            ));
        }
        for (edge, _) in &mut converted {
            edge.sources.sort();
            edge.sources.dedup();
            edge.targets.sort();
            edge.targets.dedup();
        }
        converted.sort_by_cached_key(|(edge, _)| {
            serde_json::to_string(edge).expect("serializable hyperedge")
        });
        let mut metadata = BTreeMap::new();
        for (edge, conditions) in converted {
            if let Some(conditions) = conditions {
                metadata.insert(
                    format!("edge_{}", graph.edges.len()),
                    conditions.debug_repr(ctxt),
                );
            }
            graph.edges.push(edge);
        }
        (graph, metadata)
    }
}
