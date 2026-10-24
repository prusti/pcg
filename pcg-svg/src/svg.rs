use std::fmt::Write;

use crate::{Drawing, Hypergraph, Path, PathSegment, Point, Rect, Shape};

fn escape(text: &str) -> String {
    let mut out = String::new();
    for c in text.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&apos;"),
            '\t' | '\n' | '\r' => out.push(c),
            c if c < '\u{20}' || c == '\u{fffe}' || c == '\u{ffff}' => out.push('\u{fffd}'),
            c => out.push(c),
        }
    }
    out
}

fn rect(out: &mut String, r: Rect, extra: &str) {
    write!(
        out,
        "<rect x=\"{:.2}\" y=\"{:.2}\" width=\"{:.2}\" height=\"{:.2}\" {extra}/>",
        r.x, r.y, r.width, r.height
    )
    .unwrap();
}

fn path(out: &mut String, path: &Path, id: usize) {
    write!(
        out,
        "<path fill=\"none\" d=\"M {:.2},{:.2} ",
        path.start.x, path.start.y
    )
    .unwrap();
    for segment in &path.segments {
        match segment {
            PathSegment::Line(p) => write!(out, "L {:.2},{:.2} ", p.x, p.y).unwrap(),
            PathSegment::Quadratic { control, end } => write!(
                out,
                "Q {:.2},{:.2} {:.2},{:.2} ",
                control.x, control.y, end.x, end.y
            )
            .unwrap(),
        }
    }
    out.push('"');
    if path.arrow {
        write!(out, " marker-end=\"url(#arrow_{id})\"").unwrap();
    }
    out.push_str("/>");
}

fn text(out: &mut String, center: Point, label: &str, suffix: Option<&str>) {
    let lines: Vec<_> = if label.is_empty() {
        vec![""]
    } else {
        label.lines().collect()
    };
    write!(out, "<text text-anchor=\"middle\" stroke=\"none\">").unwrap();
    for (i, line) in lines.iter().enumerate() {
        let y = center.y + 5.0 + (i as f64 - (lines.len() - 1) as f64 / 2.0) * 18.0;
        write!(
            out,
            "<tspan x=\"{:.2}\" y=\"{y:.2}\">{}",
            center.x,
            escape(line)
        )
        .unwrap();
        if i + 1 == lines.len()
            && let Some(suffix) = suffix
        {
            write!(
                out,
                ": <tspan font-weight=\"bold\">{}</tspan>",
                escape(suffix)
            )
            .unwrap();
        }
        out.push_str("</tspan>");
    }
    out.push_str("</text>");
}

pub(crate) fn render(graph: &Hypergraph, drawing: &Drawing) -> String {
    let b = drawing.bounds;
    let mut out = format!(
        "<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"{:.2} {:.2} {:.2} {:.2}\" width=\"{:.2}\" height=\"{:.2}\" role=\"img\" aria-label=\"Place capability graph\" font-family=\"DejaVu Sans Mono,monospace\" font-size=\"14\"><defs>",
        b.x, b.y, b.width, b.height, b.width, b.height
    );
    for (i, edge) in graph.edges.iter().enumerate() {
        write!(out, "<marker id=\"arrow_{i}\" viewBox=\"0 0 10 10\" refX=\"9\" refY=\"5\" markerWidth=\"7\" markerHeight=\"7\" orient=\"auto\"><path d=\"M 0 0 L 10 5 L 0 10 z\" fill=\"{}\"/></marker>", edge.color.css()).unwrap();
    }
    out.push_str("</defs>");
    rect(&mut out, b, "fill=\"white\"");
    for (i, (edge, route)) in graph.edges.iter().zip(&drawing.edges).enumerate() {
        let color = edge.color.css();
        let width = if edge.thick { 3.0 } else { 1.6 };
        let dash = if edge.dashed {
            " stroke-dasharray=\"6 4\""
        } else {
            ""
        };
        write!(out, "<g id=\"edge_{i}\" class=\"edge\" stroke=\"{color}\" stroke-width=\"{width}\" fill=\"{color}\" stroke-linejoin=\"round\"{dash}><title>{}</title>", escape(&edge.tooltip)).unwrap();
        for (name, endpoint) in [("source", &route.source), ("target", &route.target)] {
            if let Some(enclosure) = endpoint.enclosure {
                let members = endpoint
                    .members
                    .iter()
                    .map(|n| n.0.to_string())
                    .collect::<Vec<_>>()
                    .join(" ");
                rect(
                    &mut out,
                    enclosure,
                    &format!(
                        "id=\"set_{i}_{name}\" class=\"node-set\" data-members=\"{members}\" fill=\"none\" rx=\"5\""
                    ),
                );
            }
        }
        for curve in &route.paths {
            path(&mut out, curve, i);
        }
        out.push_str("</g>");
    }
    for (i, (node, &bounds)) in graph.nodes.iter().zip(&drawing.nodes).enumerate() {
        let color = node.color.css();
        write!(out, "<g id=\"node_{i}\" class=\"node\" stroke=\"{color}\" stroke-width=\"1.5\" fill=\"{color}\"><title>{}</title>", escape(&node.tooltip)).unwrap();
        if node.shape == Shape::Octagon {
            let Rect {
                x,
                y,
                width: w,
                height: h,
            } = bounds;
            let c = 7.0;
            let vertices = [
                (x + c, y),
                (x + w - c, y),
                (x + w, y + c),
                (x + w, y + h - c),
                (x + w - c, y + h),
                (x + c, y + h),
                (x, y + h - c),
                (x, y + c),
            ];
            out.push_str("<polygon fill=\"white\" points=\"");
            for (x, y) in vertices {
                write!(out, "{x:.2},{y:.2} ").unwrap();
            }
            out.push_str("\"/>");
        } else {
            rect(
                &mut out,
                bounds,
                if node.shape == Shape::Rounded {
                    "fill=\"white\" rx=\"12\""
                } else {
                    "fill=\"white\""
                },
            );
        }
        text(
            &mut out,
            Point::new(
                bounds.x + bounds.width / 2.0,
                bounds.y + bounds.height / 2.0,
            ),
            &node.label,
            node.suffix.as_deref(),
        );
        out.push_str("</g>");
    }
    for (i, (edge, route)) in graph.edges.iter().zip(&drawing.edges).enumerate() {
        if edge.label.is_empty() {
            continue;
        }
        write!(out, "<g id=\"edge_{i}_label\" data-edge-id=\"edge_{i}\" class=\"edge-label\"><title>{}</title>", escape(&edge.tooltip)).unwrap();
        text(&mut out, route.label.center(), &edge.label, None);
        out.push_str("</g>");
    }
    out.push_str("</svg>\n");
    out
}
