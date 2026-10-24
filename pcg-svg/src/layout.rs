use std::collections::{BTreeMap, BTreeSet};

use crate::{Hypergraph, NodeId, Path, routing};

pub use graphlay::Point;

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Rect {
    pub x: f64,
    pub y: f64,
    pub width: f64,
    pub height: f64,
}

impl Rect {
    pub fn center(self) -> Point {
        Point::new(self.x + self.width / 2.0, self.y + self.height / 2.0)
    }
    pub(crate) fn from_center(center: Point, size: graphlay::Size) -> Self {
        Self {
            x: center.x - size.width / 2.0,
            y: center.y - size.height / 2.0,
            width: size.width,
            height: size.height,
        }
    }
}

const NODE_GAP: f64 = 36.0;
const FONT_SIZE: f64 = 14.0;

#[derive(Debug)]
pub enum LayoutError {
    EmptyEndpoint { edge: usize },
    UnknownNode { edge: usize, node: NodeId },
    TooManyNodes,
    Engine(graphlay::LayoutError),
}

impl std::fmt::Display for LayoutError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptyEndpoint { edge } => write!(f, "hyperedge {edge} has an empty endpoint"),
            Self::UnknownNode { edge, node } => {
                write!(f, "hyperedge {edge} references unknown node {}", node.0)
            }
            Self::TooManyNodes => write!(f, "too many nodes for the layout engine"),
            Self::Engine(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for LayoutError {}

#[derive(Clone, Debug)]
pub struct Endpoint {
    pub members: Vec<NodeId>,
    /// None means that this endpoint uses explicit branches instead of a box.
    pub enclosure: Option<Rect>,
    pub branches: Vec<Vec<Point>>,
}

#[derive(Clone, Debug)]
pub struct RoutedEdge {
    pub source: Endpoint,
    pub target: Endpoint,
    /// Routing waypoints between the endpoint groups.
    pub path: Vec<Point>,
    /// Complete paths, including endpoint branches and obstacle-aware curves.
    pub paths: Vec<Path>,
    pub label: Rect,
}

#[derive(Clone, Debug)]
pub struct Drawing {
    pub nodes: Vec<Rect>,
    pub edges: Vec<RoutedEdge>,
    pub bounds: Rect,
}

pub(crate) fn text_size(text: &str) -> graphlay::Size {
    graphlay::Size::new(
        text.lines()
            .map(|line| line.chars().count())
            .max()
            .unwrap_or(0) as f64
            * FONT_SIZE
            * 0.62
            + 16.0,
        text.lines().count().max(1) as f64 * 18.0 + 12.0,
    )
}

fn root(parents: &[usize], mut i: usize) -> usize {
    while parents[i] != i {
        i = parents[i];
    }
    i
}

fn endpoint_members(graph: &Hypergraph) -> Result<Vec<[Vec<NodeId>; 2]>, LayoutError> {
    graph
        .edges
        .iter()
        .enumerate()
        .map(|(edge, e)| {
            let mut ends = [e.sources.clone(), e.targets.clone()];
            for members in &mut ends {
                members.sort();
                members.dedup();
                if members.is_empty() {
                    return Err(LayoutError::EmptyEndpoint { edge });
                }
                for &node in members.iter() {
                    if node.0 >= graph.nodes.len() {
                        return Err(LayoutError::UnknownNode { edge, node });
                    }
                }
            }
            Ok(ends)
        })
        .collect()
}

// Penalize nonmembers between a set's first and last members. Adjacent swaps
// improve overlapping sets without trying every permutation of a large group.
fn order_members(members: &mut [usize], sets: &[Vec<NodeId>]) {
    let cost = |order: &[usize]| -> usize {
        sets.iter()
            .map(|set| {
                let positions: Vec<_> = order
                    .iter()
                    .enumerate()
                    .filter(|(_, n)| set.binary_search(&NodeId(**n)).is_ok())
                    .map(|(i, _)| i)
                    .collect();
                match (positions.first(), positions.last()) {
                    (Some(first), Some(last)) => last - first + 1 - positions.len(),
                    _ => 0,
                }
            })
            .sum()
    };
    let mut best = cost(members);
    for _ in 0..8 {
        let mut changed = false;
        for i in 1..members.len() {
            members.swap(i - 1, i);
            let next = cost(members);
            if next < best {
                best = next;
                changed = true;
            } else {
                members.swap(i - 1, i);
            }
        }
        if !changed {
            break;
        }
    }
}

pub(crate) fn layout(graph: &Hypergraph) -> Result<Drawing, LayoutError> {
    if graph.nodes.len() > u32::MAX as usize {
        return Err(LayoutError::TooManyNodes);
    }
    let ends = endpoint_members(graph)?;
    let sets: Vec<_> = ends
        .iter()
        .flatten()
        .filter(|set| set.len() > 1)
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();

    // Contract co-members for the layered layout, then expand each group into a
    // row. Shared members remain single nodes in the expanded drawing.
    let mut parents: Vec<_> = (0..graph.nodes.len()).collect();
    for set in &sets {
        for member in &set[1..] {
            let a = root(&parents, set[0].0);
            let b = root(&parents, member.0);
            parents[a.max(b)] = a.min(b);
        }
    }
    let mut groups = BTreeMap::<usize, Vec<usize>>::new();
    for i in 0..graph.nodes.len() {
        groups.entry(root(&parents, i)).or_default().push(i);
    }
    let mut builder = graphlay::GraphBuilder::new();
    let mut group_of = vec![graphlay::NodeId(0); graph.nodes.len()];
    let mut local = vec![Point::new(0.0, 0.0); graph.nodes.len()];
    let sizes: Vec<_> = graph
        .nodes
        .iter()
        .map(|node| {
            let text = match &node.suffix {
                Some(suffix) => format!("{}: {suffix}", node.label),
                None => node.label.clone(),
            };
            let mut size = text_size(&text);
            if node.shape == crate::Shape::Octagon {
                size.width += 12.0;
            }
            size
        })
        .collect();
    let mut paddings = BTreeMap::<Vec<NodeId>, f64>::new();
    for (leader, members) in &mut groups {
        let group_sets: Vec<_> = sets
            .iter()
            .filter(|s| root(&parents, s[0].0) == *leader)
            .cloned()
            .collect();
        order_members(members, &group_sets);
        let padding = 16.0 + group_sets.len() as f64 * 4.0;
        for (i, set) in group_sets.into_iter().enumerate() {
            paddings.insert(set, 10.0 + i as f64 * 4.0);
        }
        let width = members.iter().map(|&n| sizes[n].width).sum::<f64>()
            + NODE_GAP * members.len().saturating_sub(1) as f64;
        let height = members.iter().map(|&n| sizes[n].height).fold(0.0, f64::max);
        let group = builder.add_box(graphlay::Size::new(
            width + padding * 2.0,
            height + padding * 2.0,
        ));
        let mut x = -width / 2.0;
        for &n in members.iter() {
            local[n] = Point::new(x + sizes[n].width / 2.0, 0.0);
            group_of[n] = group;
            x += sizes[n].width + NODE_GAP;
        }
    }
    for (edge, [source, target]) in graph.edges.iter().zip(&ends) {
        let a = group_of[source[0].0];
        let b = group_of[target[0].0];
        builder.add_edge(graphlay::Edge {
            label_size: (!edge.label.is_empty()).then(|| text_size(&edge.label)),
            source_port: Some(graphlay::PortHint::Side(if a == b {
                graphlay::Side::Top
            } else {
                graphlay::Side::Bottom
            })),
            target_port: Some(graphlay::PortHint::Side(graphlay::Side::Top)),
            ..graphlay::Edge::new(a, b)
        });
    }
    let mut options = graphlay::LayoutOptions::layered_default();
    options.direction = graphlay::Direction::TopBottom;
    options.routing.style = graphlay::RoutingStyle::Diagonal;
    options.spacing.layer_gap = 70.0;
    let placed = graphlay::layout(&builder.build(), &options).map_err(LayoutError::Engine)?;
    let nodes: Vec<_> = local
        .iter()
        .enumerate()
        .map(|(i, offset)| {
            let center = placed.nodes[group_of[i].index()].center;
            Rect::from_center(Point::new(center.x + offset.x, center.y), sizes[i])
        })
        .collect();
    let mut bounds = Rect {
        x: placed.bounds.min.x,
        y: placed.bounds.min.y,
        width: placed.bounds.width(),
        height: placed.bounds.height(),
    };
    let mut edges = Vec::new();
    for ((edge, ends), route) in graph.edges.iter().zip(ends).zip(&placed.edges) {
        let [source, target] = ends;
        let first = route.points[0];
        let last = *route.points.last().unwrap();
        let source_side = route.source_port.as_ref().unwrap().side;
        let target_side = route.target_port.as_ref().unwrap().side;
        let source = endpoint(source, &nodes, &paddings, first, source_side);
        let target = endpoint(target, &nodes, &paddings, last, target_side);
        let label = route.label_anchor.unwrap_or(Point::new(
            (first.x + last.x) / 2.0,
            (first.y + last.y) / 2.0,
        ));
        let label = Rect::from_center(
            label,
            if edge.label.is_empty() {
                graphlay::Size::new(0.0, 0.0)
            } else {
                text_size(&edge.label)
            },
        );
        for end in [&source, &target] {
            if let Some(rect) = end.enclosure {
                bounds = union(bounds, rect);
            }
        }
        edges.push(RoutedEdge {
            source,
            target,
            path: route.points.clone(),
            paths: Vec::new(),
            label,
        });
    }
    // Route and label against the expanded nodes and set outlines.
    let mut obstacles = nodes.clone();
    for edge in &edges {
        obstacles.extend(
            [edge.source.enclosure, edge.target.enclosure]
                .into_iter()
                .flatten(),
        );
    }
    routing::route(&mut edges, &nodes, &obstacles);
    for point in edges
        .iter()
        .flat_map(|edge| &edge.paths)
        .flat_map(Path::flattened)
    {
        // Include the approximation tolerance around every point on a curve.
        bounds = union(
            bounds,
            Rect {
                x: point.x - 0.25,
                y: point.y - 0.25,
                width: 0.5,
                height: 0.5,
            },
        );
    }
    let segments: Vec<_> = edges
        .iter()
        .flat_map(|edge| &edge.paths)
        .flat_map(|path| {
            path.flattened()
                .windows(2)
                .map(|p| (p[0], p[1]))
                .collect::<Vec<_>>()
        })
        .collect();
    for (edge, route) in graph.edges.iter().zip(&mut edges) {
        if edge.label.is_empty() {
            continue;
        }
        let size = text_size(&edge.label);
        route.label = place_label(route, size, &obstacles, &segments);
        obstacles.push(route.label);
        bounds = union(bounds, route.label);
    }
    if graph.nodes.is_empty() {
        bounds = Rect::from_center(Point::new(0.0, 0.0), graphlay::Size::new(80.0, 40.0));
    }
    Ok(Drawing {
        nodes,
        edges,
        bounds: expand(bounds, 24.0),
    })
}

pub(crate) fn union(a: Rect, b: Rect) -> Rect {
    Rect {
        x: a.x.min(b.x),
        y: a.y.min(b.y),
        width: (a.x + a.width).max(b.x + b.width) - a.x.min(b.x),
        height: (a.y + a.height).max(b.y + b.height) - a.y.min(b.y),
    }
}

pub(crate) fn expand(r: Rect, p: f64) -> Rect {
    Rect {
        x: r.x - p,
        y: r.y - p,
        width: r.width + 2.0 * p,
        height: r.height + 2.0 * p,
    }
}

pub(crate) fn intersects(a: Rect, b: Rect) -> bool {
    a.x < b.x + b.width && b.x < a.x + a.width && a.y < b.y + b.height && b.y < a.y + a.height
}

fn place_label(
    route: &RoutedEdge,
    size: graphlay::Size,
    obstacles: &[Rect],
    segments: &[(Point, Point)],
) -> Rect {
    let mut own_segments: Vec<_> = route
        .paths
        .iter()
        .flat_map(|path| {
            path.flattened()
                .windows(2)
                .map(|p| (p[0], p[1]))
                .collect::<Vec<_>>()
        })
        .filter(|(a, b)| (b.x - a.x).hypot(b.y - a.y) > 0.001)
        .collect();
    own_segments.sort_by(|(a, b), (c, d)| {
        (d.x - c.x)
            .hypot(d.y - c.y)
            .total_cmp(&(b.x - a.x).hypot(b.y - a.y))
    });
    if own_segments.is_empty() {
        let p = route.label.center();
        own_segments.push((p, Point::new(p.x, p.y + 1.0)));
    }
    let mut clearance = 6.0;
    loop {
        for &(a, b) in &own_segments {
            let length = (b.x - a.x).hypot(b.y - a.y);
            let normal = Point::new((b.y - a.y) / length, (a.x - b.x) / length);
            let offset =
                (normal.x.abs() * size.width + normal.y.abs() * size.height) / 2.0 + clearance;
            for fraction in [0.5, 0.35, 0.65] {
                for side in [1.0, -1.0] {
                    let center = Point::new(
                        a.x + (b.x - a.x) * fraction + normal.x * offset * side,
                        a.y + (b.y - a.y) * fraction + normal.y * offset * side,
                    );
                    let rect = Rect::from_center(center, size);
                    if obstacles
                        .iter()
                        .all(|&other| !intersects(expand(other, 3.0), rect))
                        && segments
                            .iter()
                            .all(|&(a, b)| !routing::segment_intersects(a, b, expand(rect, 3.0)))
                    {
                        return rect;
                    }
                }
            }
        }
        clearance += size.height + 8.0;
    }
}

fn endpoint(
    members: Vec<NodeId>,
    nodes: &[Rect],
    paddings: &BTreeMap<Vec<NodeId>, f64>,
    port: Point,
    side: graphlay::Side,
) -> Endpoint {
    let bounds = members.iter().map(|n| nodes[n.0]).reduce(union).unwrap();
    let enclosure = if members.len() > 1 {
        let rect = expand(bounds, paddings[&members]);
        nodes
            .iter()
            .enumerate()
            .all(|(i, &node)| members.binary_search(&NodeId(i)).is_ok() || !intersects(rect, node))
            .then_some(rect)
    } else {
        None
    };
    let boxes = match enclosure {
        Some(rect) => vec![rect],
        None => members.iter().map(|n| nodes[n.0]).collect(),
    };
    let branches = boxes
        .iter()
        .map(|b| {
            let x = b.x + b.width / 2.0;
            let y = if side == graphlay::Side::Top {
                b.y
            } else {
                b.y + b.height
            };
            vec![Point::new(x, y), Point::new(x, port.y), port]
        })
        .collect();
    Endpoint {
        members,
        enclosure,
        branches,
    }
}
