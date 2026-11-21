use crate::{Endpoint, Point, Rect, RoutedEdge, layout::intersects};

#[derive(Clone, Debug)]
pub enum PathSegment {
    Line(Point),
    Quadratic { control: Point, end: Point },
}

#[derive(Clone, Debug)]
pub struct Path {
    pub start: Point,
    pub segments: Vec<PathSegment>,
    pub arrow: bool,
}

impl Path {
    /// Approximates curves with line segments to within 0.25 pixels.
    pub fn flattened(&self) -> Vec<Point> {
        let mut points = vec![self.start];
        for segment in &self.segments {
            match *segment {
                PathSegment::Line(end) => points.push(end),
                PathSegment::Quadratic { control, end } => {
                    flatten(*points.last().unwrap(), control, end, &mut points);
                }
            }
        }
        points
    }
}

fn interpolate(a: Point, b: Point, fraction: f64) -> Point {
    Point::new(a.x + (b.x - a.x) * fraction, a.y + (b.y - a.y) * fraction)
}

fn distance(a: Point, b: Point) -> f64 {
    (b.x - a.x).hypot(b.y - a.y)
}

fn flatten(a: Point, b: Point, c: Point, points: &mut Vec<Point>) {
    let ab = interpolate(a, b, 0.5);
    let bc = interpolate(b, c, 0.5);
    let middle = interpolate(ab, bc, 0.5);
    if distance(middle, interpolate(a, c, 0.5)) <= 0.25 {
        points.push(c);
    } else {
        flatten(a, ab, middle, points);
        flatten(middle, bc, c, points);
    }
}

fn quadratic_intersects(a: Point, b: Point, c: Point, rect: Rect) -> bool {
    let mut cuts = vec![0.0, 1.0];
    for (start, control, end, boundaries) in [
        (a.x, b.x, c.x, [rect.x, rect.x + rect.width]),
        (a.y, b.y, c.y, [rect.y, rect.y + rect.height]),
    ] {
        let quadratic = start - 2.0 * control + end;
        let linear = 2.0 * (control - start);
        for boundary in boundaries {
            let constant = start - boundary;
            if quadratic.abs() < 1e-9 {
                if linear.abs() > 1e-9 {
                    cuts.push(-constant / linear);
                }
            } else {
                let discriminant = linear * linear - 4.0 * quadratic * constant;
                if discriminant >= 0.0 {
                    cuts.push((-linear - discriminant.sqrt()) / (2.0 * quadratic));
                    cuts.push((-linear + discriminant.sqrt()) / (2.0 * quadratic));
                }
            }
        }
    }
    cuts.retain(|t| (0.0..=1.0).contains(t));
    cuts.sort_by(f64::total_cmp);
    // Boundary crossings divide the curve into intervals that are entirely
    // inside or outside the rectangle. Test one point in each interval.
    cuts.windows(2).any(|interval| {
        let t = (interval[0] + interval[1]) / 2.0;
        let p = interpolate(interpolate(a, b, t), interpolate(b, c, t), t);
        p.x > rect.x + 1e-6
            && p.x < rect.x + rect.width - 1e-6
            && p.y > rect.y + 1e-6
            && p.y < rect.y + rect.height - 1e-6
    })
}

fn continuous_curve(points: &[Point], arrow: bool, obstacles: &[Rect]) -> Option<Path> {
    if points.len() < 3 {
        return None;
    }
    let first = points[0];
    let last = *points.last().unwrap();
    let clear = |start, control, end| {
        obstacles.iter().all(|&rect| {
            contains(rect, first)
                || contains(rect, last)
                || !quadratic_intersects(start, control, end, rect)
        })
    };
    let chord = subtract(last, first);
    let deviation = |point| cross(chord, subtract(point, first)).abs();
    let bend = *points
        .iter()
        .max_by(|&&a, &&b| deviation(a).total_cmp(&deviation(b)))
        .unwrap();
    if distance(first, last) > 0.001 && deviation(bend) > 0.001 {
        // A single quadratic passes through the detour's furthest point at
        // its midpoint, distributing the bend over the entire edge.
        let control = Point::new(
            2.0 * bend.x - (first.x + last.x) / 2.0,
            2.0 * bend.y - (first.y + last.y) / 2.0,
        );
        if clear(first, control, last) {
            return Some(Path {
                start: first,
                segments: vec![PathSegment::Quadratic { control, end: last }],
                arrow,
            });
        }
    }
    let mut path = Path {
        start: first,
        segments: Vec::new(),
        arrow,
    };
    let mut start = path.start;
    for i in 1..points.len() - 1 {
        let control = points[i];
        let end = if i == points.len() - 2 {
            last
        } else {
            interpolate(control, points[i + 1], 0.5)
        };
        if !clear(start, control, end) {
            return None;
        }
        // Adjacent curves meet at the midpoint between their controls, giving
        // them the same tangent and derivative at every join.
        path.segments.push(PathSegment::Quadratic { control, end });
        start = end;
    }
    Some(path)
}

fn smooth(mut points: Vec<Point>, arrow: bool, obstacles: &[Rect]) -> Path {
    points.dedup_by(|a, b| distance(*a, *b) < 0.001);
    let mut simplified: Vec<Point> = Vec::new();
    for p in points {
        while simplified.len() >= 2 {
            let a = simplified[simplified.len() - 2];
            let b = simplified[simplified.len() - 1];
            let cross = (b.x - a.x) * (p.y - b.y) - (b.y - a.y) * (p.x - b.x);
            let dot = (b.x - a.x) * (p.x - b.x) + (b.y - a.y) * (p.y - b.y);
            if cross.abs() > 1e-6 || dot < 0.0 {
                break;
            }
            simplified.pop();
        }
        simplified.push(p);
    }
    let points = simplified;
    if let Some(path) = continuous_curve(&points, arrow, obstacles) {
        return path;
    }
    let mut path = Path {
        start: points[0],
        segments: Vec::new(),
        arrow,
    };
    for corner in points.windows(3) {
        let [a, b, c] = [corner[0], corner[1], corner[2]];
        let incoming = distance(a, b);
        let outgoing = distance(b, c);
        let trim = 32.0_f64.min(incoming * 0.45).min(outgoing * 0.45);
        let entry = interpolate(b, a, trim / incoming);
        let exit = interpolate(b, c, trim / outgoing);
        // A quadratic stays inside the convex hull of its three control points.
        // Keep that hull's bounding box clear of nodes and endpoint enclosures.
        let bounds = Rect {
            x: entry.x.min(b.x).min(exit.x),
            y: entry.y.min(b.y).min(exit.y),
            width: entry.x.max(b.x).max(exit.x) - entry.x.min(b.x).min(exit.x),
            height: entry.y.max(b.y).max(exit.y) - entry.y.min(b.y).min(exit.y),
        };
        if obstacles.iter().any(|&r| intersects(bounds, r)) {
            path.segments.push(PathSegment::Line(b));
        } else {
            path.segments.push(PathSegment::Line(entry));
            path.segments.push(PathSegment::Quadratic {
                control: b,
                end: exit,
            });
        }
    }
    if points.len() > 1 {
        path.segments
            .push(PathSegment::Line(*points.last().unwrap()));
    }
    path
}

fn paths(edge: &RoutedEdge, nodes: &[Rect], obstacles: &[Rect]) -> Vec<Path> {
    let mut paths = Vec::new();
    let mut main = Vec::new();
    if let [branch] = &edge.source.branches[..] {
        main.extend(branch);
    } else {
        paths.extend(
            edge.source
                .branches
                .iter()
                .map(|branch| smooth(branch.clone(), false, obstacles)),
        );
    }
    main.extend(&edge.path);
    let arrow = edge.target.branches.len() == 1;
    if let [branch] = &edge.target.branches[..] {
        main.extend(branch.iter().rev());
    } else {
        paths.extend(
            edge.target
                .branches
                .iter()
                .map(|branch| smooth(branch.iter().rev().copied().collect(), true, obstacles)),
        );
    }
    if direct(edge, nodes, obstacles).is_none()
        && let Some((source, target)) = endpoint_boxes(edge, nodes)
    {
        main = attach_to_endpoints(main, source, target, nodes, &obstacles[nodes.len()..]);
    }
    paths.push(smooth(main, arrow, obstacles));
    paths
}

fn endpoint_box(endpoint: &Endpoint, nodes: &[Rect]) -> Option<Rect> {
    endpoint
        .enclosure
        .or_else(|| (endpoint.members.len() == 1).then(|| nodes[endpoint.members[0].0]))
}

fn endpoint_boxes(edge: &RoutedEdge, nodes: &[Rect]) -> Option<(Rect, Rect)> {
    let source = endpoint_box(&edge.source, nodes)?;
    let target = endpoint_box(&edge.target, nodes)?;
    (!intersects(source, target)).then_some((source, target))
}

fn border(rect: Rect, toward: Point) -> Point {
    let center = rect.center();
    let dx = toward.x - center.x;
    let dy = toward.y - center.y;
    let scale = (rect.width / (2.0 * dx.abs())).min(rect.height / (2.0 * dy.abs()));
    Point::new(center.x + dx * scale, center.y + dy * scale)
}

fn contains(rect: Rect, point: Point) -> bool {
    point.x > rect.x + 1e-6
        && point.x < rect.x + rect.width - 1e-6
        && point.y > rect.y + 1e-6
        && point.y < rect.y + rect.height - 1e-6
}

fn clear(
    a: Point,
    b: Point,
    source: Rect,
    target: Rect,
    nodes: &[Rect],
    outlines: &[Rect],
) -> bool {
    distance(a, b) > 0.001
        && nodes.iter().all(|&rect| !segment_intersects(a, b, rect))
        && outlines.iter().all(|&rect| {
            // An edge may enter an enclosing set to reach one of its members.
            ((rect != source && contains(rect, source.center()))
                || (rect != target && contains(rect, target.center())))
                || !segment_intersects(a, b, rect)
        })
}

fn attach_to_endpoints(
    points: Vec<Point>,
    source: Rect,
    target: Rect,
    nodes: &[Rect],
    outlines: &[Rect],
) -> Vec<Point> {
    // Reattach the detour to the visible boundaries rather than the layout
    // group's ports. Preserve its middle waypoints and separate parallel lanes.
    let mut points = points;
    if let Some((index, start)) = (1..points.len() - 1).rev().find_map(|i| {
        if contains(source, points[i]) {
            return None;
        }
        let start = border(source, points[i]);
        clear(start, points[i], source, target, nodes, outlines).then_some((i, start))
    }) {
        points.drain(..index);
        points.insert(0, start);
    }
    if let Some((index, end)) = (1..points.len() - 1).find_map(|i| {
        if contains(target, points[i]) {
            return None;
        }
        let end = border(target, points[i]);
        clear(points[i], end, source, target, nodes, outlines).then_some((i, end))
    }) {
        points.truncate(index + 1);
        points.push(end);
    }
    points
}

fn direct(edge: &RoutedEdge, nodes: &[Rect], obstacles: &[Rect]) -> Option<Path> {
    let (source, target) = endpoint_boxes(edge, nodes)?;
    let start = border(source, target.center());
    let end = border(target, source.center());
    clear(start, end, source, target, nodes, &obstacles[nodes.len()..]).then_some(Path {
        start,
        segments: vec![PathSegment::Line(end)],
        arrow: true,
    })
}

fn cross(a: Point, b: Point) -> f64 {
    a.x * b.y - a.y * b.x
}

fn subtract(a: Point, b: Point) -> Point {
    Point::new(a.x - b.x, a.y - b.y)
}

fn segments_conflict(a: Point, b: Point, c: Point, d: Point) -> bool {
    let ab = subtract(b, a);
    let cd = subtract(d, c);
    let ac = subtract(c, a);
    let denominator = cross(ab, cd);
    if denominator.abs() > 1e-6 {
        let t = cross(ac, cd) / denominator;
        let u = cross(ac, ab) / denominator;
        let within = |x: f64| (-1e-6..=1.0 + 1e-6).contains(&x);
        let interior = |x: f64| (1e-6..1.0 - 1e-6).contains(&x);
        return within(t) && within(u) && (interior(t) || interior(u));
    }
    let length = distance(a, b);
    if length < 0.001 || cross(ab, ac).abs() / length > 0.001 {
        return false;
    }
    let project = |p: Point| ((p.x - a.x) * ab.x + (p.y - a.y) * ab.y) / length;
    let from = project(c).min(project(d)).max(0.0);
    let to = project(c).max(project(d)).min(length);
    to - from > 0.001
}

fn conflicts(a: &[Path], b: &[Path]) -> bool {
    a.iter().any(|a| {
        let a = a.flattened();
        b.iter().any(|b| {
            let b = b.flattened();
            a.windows(2).any(|a| {
                b.windows(2)
                    .any(|b| segments_conflict(a[0], a[1], b[0], b[1]))
            })
        })
    })
}

pub(crate) fn route(edges: &mut [RoutedEdge], nodes: &[Rect], obstacles: &[Rect]) {
    let fallback: Vec<_> = edges
        .iter()
        .map(|edge| paths(edge, nodes, obstacles))
        .collect();
    let mut straight = Vec::new();
    for (edge, fallback) in edges.iter_mut().zip(&fallback) {
        let candidate = direct(edge, nodes, obstacles);
        straight.push(candidate.is_some());
        edge.paths = candidate.map_or_else(|| fallback.clone(), |path| vec![path]);
    }
    // Resolve conflicts against the final routes, including detours. Each pass
    // can only restore a detour; the process therefore terminates deterministically.
    loop {
        let mut changed = false;
        for i in 0..edges.len() {
            for j in i + 1..edges.len() {
                if (straight[i] || straight[j]) && conflicts(&edges[i].paths, &edges[j].paths) {
                    let restore = if straight[j] { j } else { i };
                    straight[restore] = false;
                    edges[restore].paths.clone_from(&fallback[restore]);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
}

pub(crate) fn segment_intersects(a: Point, b: Point, rect: Rect) -> bool {
    let mut start: f64 = 0.0;
    let mut end: f64 = 1.0;
    for (origin, delta, min, max) in [
        (a.x, b.x - a.x, rect.x, rect.x + rect.width),
        (a.y, b.y - a.y, rect.y, rect.y + rect.height),
    ] {
        if delta.abs() < 1e-9 {
            if origin <= min || origin >= max {
                return false;
            }
        } else {
            let near = (min - origin) / delta;
            let far = (max - origin) / delta;
            start = start.max(near.min(far));
            end = end.min(near.max(far));
            if start >= end {
                return false;
            }
        }
    }
    (end - start) * distance(a, b) > 1e-6
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn quadratic_clearance_checks_crossings_and_tangencies() {
        let a = Point::new(0.0, 0.0);
        let b = Point::new(50.0, 100.0);
        let c = Point::new(100.0, 0.0);
        let rect = |x, y, width, height| Rect {
            x,
            y,
            width,
            height,
        };
        assert!(quadratic_intersects(a, b, c, rect(15.0, 20.0, 10.0, 20.0)));
        assert!(!quadratic_intersects(a, b, c, rect(40.0, 60.0, 20.0, 20.0)));
        assert!(!quadratic_intersects(a, b, c, rect(45.0, 50.0, 10.0, 10.0)));
        assert!(quadratic_intersects(
            a,
            b,
            c,
            rect(-1.0, -1.0, 102.0, 102.0)
        ));
        assert!(quadratic_intersects(
            a,
            Point::new(50.0, 50.0),
            Point::new(100.0, 100.0),
            rect(45.0, 45.0, 10.0, 10.0)
        ));
        assert!(!quadratic_intersects(
            a,
            Point::new(0.0, 50.0),
            Point::new(0.0, 100.0),
            rect(0.0, 45.0, 10.0, 10.0)
        ));
    }
}
