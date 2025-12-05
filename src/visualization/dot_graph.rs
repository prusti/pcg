use std::{
    borrow::Cow,
    collections::{BTreeSet, HashMap},
    fmt::Display,
    fs::File,
    io::Write,
    path::Path,
    process::{Command, Stdio},
};

use serde_derive::Serialize;

use crate::{
    borrow_pcg::validity_conditions::ValidityConditionsDebugRepr,
    utils::{DebugRepr, HasCompilerCtxt, html::Html},
    visualization::Graph,
};

type NodeId = String;
#[derive(Clone, Debug, PartialEq, Eq, Hash, Ord, PartialOrd, Serialize)]
#[serde(transparent)]
pub(crate) struct DotEdgeId(String);

pub struct DotGraphWithEdgeCtxt<Ctxt> {
    pub(crate) graph: DotGraph,
    pub(crate) edge_ctxt: HashMap<DotEdgeId, Ctxt>,
}

impl DotGraphWithEdgeCtxt<ValidityConditionsDebugRepr> {
    pub(crate) fn from_graph<'a, 'tcx: 'a>(
        graph: Graph<'a>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> Self {
        let nodes = graph.nodes.iter().map(|g| g.to_dot_node()).collect();
        let mut edges = Vec::new();
        let mut edge_ctxt = HashMap::new();
        for (i, edge) in graph.edges.iter().enumerate() {
            let edge_id = DotEdgeId(format!("edge_{i}"));
            if let Some(validity_conditions) = edge.validity_conditions() {
                edge_ctxt.insert(edge_id.clone(), validity_conditions.debug_repr(ctxt));
            }
            edges.push(edge.to_dot_edge(Some(edge_id), ctxt));
        }
        Self {
            graph: DotGraph {
                name: Cow::Borrowed("graph"),
                nodes,
                edges,
            },
            edge_ctxt,
        }
    }
}

pub struct DotGraph {
    pub(crate) name: Cow<'static, str>,
    pub(crate) nodes: Vec<DotNode>,
    pub(crate) edges: Vec<DotEdge>,
}

impl DotGraph {
    pub fn write_to_file(self, path: &Path) -> Result<(), std::io::Error> {
        let mut file = File::create(path)?;
        file.write_all(self.to_string().as_bytes())?;
        Ok(())
    }
    pub fn render_with_imgcat(dot_str: &str, comment: &str) -> Result<(), std::io::Error> {
        let mut dot_process = Command::new("dot")
            .args(["-Tpng"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()?;

        let dot_stdin = dot_process
            .stdin
            .as_mut()
            .expect("Failed to open dot stdin");
        dot_stdin.write_all(dot_str.as_bytes())?;

        let dot_output = dot_process.wait_with_output()?;

        if !dot_output.status.success() {
            return Err(std::io::Error::other("dot command failed"));
        }

        let mut imgcat_process = Command::new("imgcat")
            .stdin(Stdio::piped())
            .stdout(Stdio::inherit())
            .spawn()?;

        let imgcat_stdin = imgcat_process
            .stdin
            .as_mut()
            .expect("Failed to open imgcat stdin");
        imgcat_stdin.write_all(&dot_output.stdout)?;

        let imgcat_status = imgcat_process.wait()?;

        if !imgcat_status.success() {
            return Err(std::io::Error::other("imgcat command failed"));
        }
        tracing::info!("↑ {} ↑\n", comment);

        Ok(())
    }
}

pub struct RankAnnotation {
    pub rank_type: String,
    pub nodes: BTreeSet<NodeId>,
}

impl Display for RankAnnotation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{{ rank = {}; {}; }}",
            self.rank_type,
            self.nodes
                .iter()
                .map(|n| n.to_string())
                .collect::<Vec<_>>()
                .join("; ")
        )
    }
}

impl Display for DotGraph {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "digraph \"{}\" {{", self.name)?;
        writeln!(f)?;
        writeln!(f, "layout=dot")?;
        writeln!(f, "node [shape=rect]")?;
        for node in &self.nodes {
            writeln!(f, "{node}")?;
        }
        for edge in &self.edges {
            writeln!(f, "{edge}")?;
        }
        writeln!(f, "}}")
    }
}

#[derive(Eq, PartialEq, PartialOrd, Ord)]
pub(crate) enum DotLabel {
    Text(DotStringAttr),
    Html(Html),
}

impl Display for DotLabel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DotLabel::Text(text) => write!(f, "{text}"),
            DotLabel::Html(html) => write!(f, "<{html}>"),
        }
    }
}

impl DotAttr for DotLabel {}

pub struct DotNode {
    pub id: NodeId,
    pub(crate) label: DotLabel,
    pub font_color: DotStringAttr,
    pub color: DotStringAttr,
    pub shape: DotStringAttr,
    pub style: Option<DotStringAttr>,
    pub penwidth: Option<DotFloatAttr>,
    pub tooltip: Option<DotStringAttr>,
}

impl DotNode {
    pub(crate) fn simple(id: NodeId, label: impl Into<Cow<'static, str>>) -> Self {
        Self {
            id,
            label: DotLabel::Text(DotStringAttr(label.into())),
            font_color: DotStringAttr("black".into()),
            color: DotStringAttr("black".into()),
            shape: DotStringAttr("rect".into()),
            style: None,
            penwidth: None,
            tooltip: None,
        }
    }
}
trait DotAttr: Display {}

#[derive(Eq, PartialEq, PartialOrd, Ord)]
pub struct DotStringAttr(pub Cow<'static, str>);

impl From<&'static str> for DotStringAttr {
    fn from(value: &'static str) -> Self {
        Self(value.into())
    }
}

impl Display for DotStringAttr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "\"{}\"", self.0.replace("\"", "\\\""))
    }
}
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dotstring_attr_escapes_quotes() {
        let attr = DotStringAttr("extern \"RustCall\"".into());
        assert_eq!(attr.to_string(), "\"extern \\\"RustCall\\\"\"");
    }
}

impl DotAttr for DotStringAttr {}

pub struct DotFloatAttr(pub f64);

impl Display for DotFloatAttr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl DotAttr for DotFloatAttr {}

fn format_attr<T: DotAttr>(name: &'static str, value: &T) -> String {
    format!("{name}={value}")
}

fn format_optional<T: DotAttr>(name: &'static str, value: &Option<T>) -> String {
    match value {
        Some(value) => format!("{name}={value}"),
        None => String::new(),
    }
}

impl Display for DotNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let attrs = [
            format_attr("label", &self.label),
            format_attr("fontcolor", &self.font_color),
            format_attr("color", &self.color),
            format_attr("shape", &self.shape),
            format_optional("style", &self.style),
            format_optional("penwidth", &self.penwidth),
            format_optional("tooltip", &self.tooltip),
        ]
        .into_iter()
        .filter(|s| !s.is_empty())
        .collect::<Vec<_>>();
        write!(f, "\"{}\" [{}]", self.id, attrs.join(", "))
    }
}

#[derive(Eq, PartialEq, PartialOrd, Ord)]
pub enum EdgeDirection {
    Forward,
    Backward,
}

#[derive(Eq, PartialEq, PartialOrd, Ord)]
pub(crate) struct EdgeOptions {
    label: DotLabel,
    color: Option<Cow<'static, str>>,
    style: Option<Cow<'static, str>>,
    direction: Option<EdgeDirection>,
    tooltip: Option<Cow<'static, str>>,
    penwidth: Option<String>,
    weight: Option<String>,
}

impl EdgeOptions {
    pub fn directed(direction: EdgeDirection) -> Self {
        Self {
            label: DotLabel::Text(DotStringAttr("".into())),
            color: None,
            style: None,
            direction: Some(direction),
            tooltip: None,
            penwidth: None,
            weight: None,
        }
    }

    pub fn undirected() -> Self {
        Self {
            label: DotLabel::Text(DotStringAttr("".into())),
            color: None,
            style: None,
            direction: None,
            tooltip: None,
            penwidth: None,
            weight: None,
        }
    }

    pub fn with_penwidth(mut self, penwidth: f64) -> Self {
        self.penwidth = Some(penwidth.to_string());
        self
    }

    pub fn with_label(mut self, label: impl Into<Cow<'static, str>>) -> Self {
        self.label = DotLabel::Text(DotStringAttr(label.into()));
        self
    }

    pub fn with_color(mut self, color: Cow<'static, str>) -> Self {
        self.color = Some(color);
        self
    }

    pub fn with_style(mut self, style: impl Into<Cow<'static, str>>) -> Self {
        self.style = Some(style.into());
        self
    }

    pub fn with_tooltip(mut self, tooltip: Cow<'static, str>) -> Self {
        self.tooltip = Some(tooltip);
        self
    }
}

#[derive(Eq, PartialEq, PartialOrd, Ord)]
pub(crate) struct DotEdge {
    pub id: Option<DotEdgeId>,
    pub from: NodeId,
    pub to: NodeId,
    pub options: EdgeOptions,
}

impl Display for DotEdge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let id_part = match &self.id {
            Some(id) => format!(", id=\"{}\"", id.0),
            None => String::new(),
        };
        let style_part = match &self.options.style {
            Some(style) => format!(", style=\"{style}\""),
            None => String::new(),
        };
        let direction_part = match &self.options.direction {
            Some(EdgeDirection::Backward) => ", dir=\"back\"",
            Some(EdgeDirection::Forward) => "",
            None => "dir=\"none\", constraint=false",
        };
        let color_part = match &self.options.color {
            Some(color) => format!(", color=\"{color}\""),
            None => String::new(),
        };
        let tooltip_part = match &self.options.tooltip {
            Some(tooltip) => format!(", edgetooltip=\"{tooltip}\""),
            None => String::new(),
        };
        let penwidth_part = match &self.options.penwidth {
            Some(penwidth) => format!(", penwidth=\"{penwidth}\""),
            None => String::new(),
        };
        let weight_part = match &self.options.weight {
            Some(weight) => format!(", weight=\"{weight}\""),
            None => String::new(),
        };
        write!(
            f,
            "    \"{}\" -> \"{}\" [label={}{}{}{}{}{}{}{}]",
            self.from,
            self.to,
            self.options.label,
            id_part,
            style_part,
            direction_part,
            color_part,
            tooltip_part,
            penwidth_part,
            weight_part
        )
    }
}
