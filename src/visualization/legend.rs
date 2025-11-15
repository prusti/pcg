use crate::{
    pcg::CapabilityKind,
    visualization::{GraphNode, NodeId, NodeType},
};

use super::dot_graph::{DotEdge, DotLabel, DotNode, DotStringAttr, EdgeDirection, EdgeOptions};
use std::io::{self, Write};

pub fn generate_edge_legend() -> io::Result<String> {
    let mut buf = vec![];
    write_edge_legend(&mut buf)?;
    Ok(String::from_utf8(buf).unwrap())
}

pub fn generate_node_legend() -> io::Result<String> {
    let mut buf = vec![];
    write_node_legend(&mut buf)?;
    Ok(String::from_utf8(buf).unwrap())
}

fn write_edge_legend<T: Write>(out: &mut T) -> io::Result<()> {
    writeln!(out, "digraph edge_legend {{")?;
    writeln!(out, "  node [shape=rect];")?;
    writeln!(out, "  rankdir=TB;")?;
    writeln!(out, "  label=\"Edge Types\";")?;
    writeln!(out, "  labelloc=\"t\";")?;
    writeln!(out, "  nodesep=0.5;")?;
    writeln!(out, "  ranksep=2.0;")?;

    // Create all clusters first
    // Projection Edge
    write_edge(
        out,
        "proj_a",
        "proj_b",
        "Projection Edge",
        EdgeOptions::undirected(),
    )?;

    // Reborrow Edge
    write_edge(
        out,
        "reborrow_a",
        "reborrow_b",
        "Reborrow Edge",
        EdgeOptions::directed(EdgeDirection::Forward)
            .with_color("orange".into())
            .with_label("region")
            .with_tooltip("conditions".into()),
    )?;

    // Deref Expansion Edge
    write_edge(
        out,
        "deref_a",
        "deref_b",
        "Deref Expansion Edge",
        EdgeOptions::undirected()
            .with_color("green".into())
            .with_tooltip("conditions".into()),
    )?;

    // Abstract Edge
    write_edge(
        out,
        "abstract_a",
        "abstract_b",
        "Abstract Edge",
        EdgeOptions::directed(EdgeDirection::Forward),
    )?;

    // Region Projection Member Edge
    write_edge(
        out,
        "region_a",
        "region_b",
        "Region Projection Edge",
        EdgeOptions::directed(EdgeDirection::Forward).with_color("purple".into()),
    )?;

    // Coupled Edge
    write_edge(
        out,
        "coupled_a",
        "coupled_b",
        "Coupled Edge",
        EdgeOptions::undirected()
            .with_color("red".into())
            .with_style("dashed"),
    )?;

    writeln!(out, "}}")
}

fn write_node_legend<T: Write>(out: &mut T) -> io::Result<()> {
    writeln!(out, "digraph node_legend {{")?;
    writeln!(out, "  node [shape=rect];")?;
    writeln!(out, "  rankdir=TB;")?;
    writeln!(out, "  label=\"Node Types\";")?;
    writeln!(out, "  labelloc=\"t\";")?;

    // Create nodes
    let owned_node = GraphNode {
        id: NodeId('f', 0),
        node_type: NodeType::PlaceNode {
            owned: true,
            label: "x".to_owned(),
            capability: Some(CapabilityKind::Write),
            location: None,
            ty: "&'a mut i32".to_owned(),
        },
    };

    let region_node = GraphNode {
        id: NodeId('r', 0),
        node_type: NodeType::RegionProjectionNode {
            label: "rx↓'rx".into(),
            base_ty: "&'rx mut i32".to_owned(),
            loans: String::new(),
        },
    };

    let borrowed_node = GraphNode {
        id: NodeId('b', 0),
        node_type: NodeType::PlaceNode {
            owned: false,
            label: "*rx".to_owned(),
            location: None,
            capability: None,
            ty: "i32".to_owned(),
        },
    };

    // Write nodes using to_dot_node()
    writeln!(out, "  {}", owned_node.to_dot_node())?;
    writeln!(out, "  {}", region_node.to_dot_node())?;
    writeln!(out, "  {}", borrowed_node.to_dot_node())?;

    // Arrange nodes horizontally
    writeln!(
        out,
        "  {{ rank=same; {}; {}; {}; }}",
        owned_node.id, region_node.id, borrowed_node.id
    )?;

    writeln!(out, "}}")
}

fn write_edge<T: Write>(
    out: &mut T,
    from: &str,
    to: &str,
    label: &str,
    options: EdgeOptions,
) -> io::Result<()> {
    let node_a = DotNode {
        id: from.to_owned(),
        label: DotLabel::Text("A".into()),
        color: DotStringAttr("black".into()),
        font_color: DotStringAttr("black".into()),
        shape: DotStringAttr("rect".into()),
        style: None,
        penwidth: None,
        tooltip: None,
    };

    let node_b = DotNode {
        id: to.to_owned(),
        label: DotLabel::Text("B".into()),
        color: DotStringAttr("black".into()),
        font_color: DotStringAttr("black".into()),
        shape: DotStringAttr("rect".into()),
        style: None,
        penwidth: None,
        tooltip: None,
    };

    let edge = DotEdge {
        id: None,
        from: from.to_owned(),
        to: to.to_owned(),
        options,
    };

    writeln!(out, "  subgraph cluster_{from} {{")?;
    writeln!(out, "    label=\"{label}\"")?;
    writeln!(out, "    {node_a}")?;
    writeln!(out, "    {node_b}")?;
    writeln!(out, "    {edge}")?;
    writeln!(out, "  }}")?;
    Ok(())
}
