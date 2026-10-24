use pcg_svg::{
    Color, Hyperedge, Hypergraph, LayoutError, Node, NodeId, PathSegment, Point, Rect, Shape,
};

fn nodes(labels: &[&str]) -> Hypergraph {
    Hypergraph {
        nodes: labels
            .iter()
            .map(|label| Node {
                label: (*label).into(),
                ..Node::default()
            })
            .collect(),
        edges: Vec::new(),
    }
}

fn edge(sources: &[usize], targets: &[usize]) -> Hyperedge {
    Hyperedge::new(
        sources.iter().copied().map(NodeId).collect(),
        targets.iter().copied().map(NodeId).collect(),
        "flow",
    )
}

fn overlaps(a: Rect, b: Rect) -> bool {
    a.x < b.x + b.width && b.x < a.x + a.width && a.y < b.y + b.height && b.y < a.y + a.height
}

fn crosses_rect(a: Point, b: Point, rect: Rect) -> bool {
    let left = rect.x + 0.001;
    let right = rect.x + rect.width - 0.001;
    let top = rect.y + 0.001;
    let bottom = rect.y + rect.height - 0.001;
    if a.x.max(b.x) <= left
        || a.x.min(b.x) >= right
        || a.y.max(b.y) <= top
        || a.y.min(b.y) >= bottom
    {
        return false;
    }
    let sides = [(left, top), (right, top), (right, bottom), (left, bottom)]
        .map(|(x, y)| (b.x - a.x) * (y - a.y) - (b.y - a.y) * (x - a.x));
    sides.iter().any(|&s| s < 0.0) && sides.iter().any(|&s| s > 0.0)
}

#[test]
fn compiler_generated_snapshot_prefers_straight_edges_and_keeps_labels_clear() {
    // test-files/026_ref_in_struct.rs, bb0_stmt_25_initial.
    let graph: Hypergraph =
        serde_json::from_str(include_str!("fixtures/ref-in-struct.json")).unwrap();
    check_geometry(&graph);
    let drawing = graph.layout().unwrap();
    assert!(drawing.edges.iter().any(|edge| {
        edge.path
            .windows(2)
            .any(|p| (p[0].x - p[1].x).abs() > 1.0 && (p[0].y - p[1].y).abs() > 1.0)
    }));
    let alias = graph
        .edges
        .iter()
        .position(|edge| {
            edge.dashed
                && graph.nodes[edge.sources[0].0].label == "x"
                && graph.nodes[edge.targets[0].0].label == "(*_5) before bb0[20]"
        })
        .unwrap();
    assert_eq!(drawing.edges[alias].paths.len(), 1);
    let curve = &drawing.edges[alias].paths[0];
    assert_eq!(
        curve.segments.len(),
        1,
        "the alias should use one continuous curve"
    );
    assert!(
        curve
            .segments
            .iter()
            .all(|segment| matches!(segment, PathSegment::Quadratic { .. }))
    );
    for (index, edge) in drawing.edges.iter().enumerate() {
        if index != alias {
            assert_eq!(edge.paths.len(), 1);
            assert!(
                matches!(edge.paths[0].segments.as_slice(), [PathSegment::Line(_)]),
                "edge {index} should be straight"
            );
        }
    }
}

fn check_geometry(graph: &Hypergraph) {
    let drawing = graph.layout().unwrap();
    assert!(
        [
            drawing.bounds.x,
            drawing.bounds.y,
            drawing.bounds.width,
            drawing.bounds.height
        ]
        .iter()
        .all(|x| x.is_finite())
    );
    for (i, &a) in drawing.nodes.iter().enumerate() {
        assert!([a.x, a.y, a.width, a.height].iter().all(|x| x.is_finite()));
        for &b in &drawing.nodes[i + 1..] {
            assert!(!overlaps(a, b), "nodes overlap: {a:?} {b:?}");
        }
    }
    for edge in &drawing.edges {
        for path in &edge.paths {
            for pair in path.segments.windows(2) {
                if let [
                    PathSegment::Quadratic {
                        control: a,
                        end: join,
                    },
                    PathSegment::Quadratic { control: b, .. },
                ] = pair
                {
                    assert!((join.x - a.x - (b.x - join.x)).abs() < 1e-6);
                    assert!((join.y - a.y - (b.y - join.y)).abs() < 1e-6);
                }
            }
            let points = path.flattened();
            for p in &points {
                assert!(p.x.is_finite() && p.y.is_finite());
                assert!(p.x >= drawing.bounds.x && p.x <= drawing.bounds.x + drawing.bounds.width);
                assert!(p.y >= drawing.bounds.y && p.y <= drawing.bounds.y + drawing.bounds.height);
            }
            for segment in points.windows(2) {
                let [a, b] = [segment[0], segment[1]];
                for node in &drawing.nodes {
                    assert!(
                        !crosses_rect(a, b, *node),
                        "edge crosses a node: {segment:?} {node:?}"
                    );
                }
            }
        }
        for endpoint in [&edge.source, &edge.target] {
            if let Some(enclosure) = endpoint.enclosure {
                for (i, &node) in drawing.nodes.iter().enumerate() {
                    assert_eq!(
                        overlaps(enclosure, node),
                        endpoint.members.contains(&NodeId(i)),
                        "incorrect enclosure membership"
                    );
                }
            }
        }
    }
    let mut labels = Vec::new();
    for (edge, route) in graph.edges.iter().zip(&drawing.edges) {
        if edge.label.is_empty() {
            continue;
        }
        let rect = route.label;
        for &other in drawing.nodes.iter().chain(&labels) {
            assert!(!overlaps(rect, other), "label collision");
        }
        for path in drawing.edges.iter().flat_map(|edge| &edge.paths) {
            for segment in path.flattened().windows(2) {
                assert!(
                    !crosses_rect(segment[0], segment[1], rect),
                    "edge crosses a label"
                );
            }
        }
        labels.push(rect);
    }
    let svg = graph.to_svg().unwrap();
    let doc = roxmltree::Document::parse(&svg).unwrap();
    assert_eq!(
        doc.descendants()
            .filter(|n| n.attribute("class") == Some("node"))
            .count(),
        graph.nodes.len()
    );
    let ids: Vec<_> = doc
        .descendants()
        .filter_map(|n| n.attribute("id"))
        .collect();
    let unique: std::collections::BTreeSet<_> = ids.iter().collect();
    assert_eq!(unique.len(), ids.len());
    assert_eq!(svg, graph.to_svg().unwrap());
}

#[test]
fn overlapping_sources_share_one_node_and_keep_two_enclosures() {
    let mut graph = nodes(&["a", "shared↓'1", "b", "*a", "*b"]);
    graph.nodes[1].shape = Shape::Octagon;
    graph.nodes[1].color = Color::Blue;
    graph.edges = vec![edge(&[0, 1], &[3]), edge(&[1, 2], &[4])];
    let drawing = graph.layout().unwrap();
    let a = drawing.edges[0].source.enclosure.unwrap();
    let b = drawing.edges[1].source.enclosure.unwrap();
    assert!(overlaps(a, b));
    check_geometry(&graph);
}

#[test]
fn incompatible_intervals_use_explicit_membership() {
    let mut graph = nodes(&["a", "b", "c", "d"]);
    graph.edges = vec![
        edge(&[0, 1], &[3]),
        edge(&[1, 2], &[3]),
        edge(&[0, 2], &[3]),
    ];
    let drawing = graph.layout().unwrap();
    assert!(
        drawing
            .edges
            .iter()
            .any(|e| e.source.enclosure.is_none() && e.source.branches.len() == 2)
    );
    check_geometry(&graph);
}

#[test]
fn cycles_self_loops_parallel_edges_and_disconnected_nodes() {
    let mut graph = nodes(&[
        "a",
        "b",
        "c",
        "disconnected",
        "very long label with Unicode ↓'1",
    ]);
    graph.edges = vec![
        edge(&[0], &[1]),
        edge(&[1], &[2]),
        edge(&[2], &[0]),
        edge(&[0], &[0]),
        edge(&[0], &[1]),
    ];
    let drawing = graph.layout().unwrap();
    assert_ne!(
        drawing.edges[0].paths[0].flattened(),
        drawing.edges[4].paths[0].flattened(),
        "parallel edges must remain distinct"
    );
    check_geometry(&graph);
    check_geometry(&Hypergraph::default());
    check_geometry(&nodes(&["alone"]));
}

#[test]
fn target_sets_and_overlapping_source_target_sets() {
    let mut graph = nodes(&["tuple", "field0", "field1", "other"]);
    graph.edges = vec![edge(&[0], &[1, 2]), edge(&[1, 2], &[2, 3])];
    check_geometry(&graph);
}

#[test]
fn rejects_invalid_endpoints_and_normalizes_duplicate_members() {
    let mut graph = nodes(&["a", "b"]);
    graph.edges.push(edge(&[], &[1]));
    assert!(matches!(
        graph.layout(),
        Err(LayoutError::EmptyEndpoint { edge: 0 })
    ));
    graph.edges[0] = edge(&[0], &[10]);
    assert!(matches!(
        graph.layout(),
        Err(LayoutError::UnknownNode { .. })
    ));
    graph.edges[0] = edge(&[0, 0], &[1, 1]);
    check_geometry(&graph);
}

#[test]
fn labels_and_tooltips_are_xml_text() {
    let mut graph = nodes(&["x<&\"'\u{1}", "y"]);
    graph.nodes[0].suffix = Some("E".into());
    graph.nodes[0].tooltip = "&'a mut Vec<T>".into();
    graph.edges.push(edge(&[0], &[1]));
    graph.edges[0].label = "x = &mut y\nsecond line".into();
    graph.edges[0].tooltip = "<script>alert('bad')</script>".into();
    check_geometry(&graph);
    let svg = graph.to_svg().unwrap();
    assert!(!svg.contains("<script>"));
    assert!(svg.contains("font-weight=\"bold\">E"));
    assert!(!svg.contains("y: </tspan>"));
}
