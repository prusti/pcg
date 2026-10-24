//! Automatic layout and SVG rendering of directed hypergraphs.
//!
//! Each node is drawn once. Hyperedge endpoints are overlapping enclosures when
//! their members form an uninterrupted interval, and explicit branches otherwise.

mod layout;
mod routing;
mod svg;

pub use layout::{Drawing, Endpoint, LayoutError, Point, Rect, RoutedEdge};
pub use routing::{Path, PathSegment};
use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct NodeId(pub usize);

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub enum Shape {
    #[default]
    Rectangle,
    Rounded,
    Octagon,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub enum Color {
    #[default]
    Black,
    Gray,
    Green,
    Blue,
    Orange,
    Purple,
    Red,
}

impl Color {
    fn css(self) -> &'static str {
        match self {
            Self::Black => "#222222",
            Self::Gray => "#777777",
            Self::Green => "#176b3a",
            Self::Blue => "#2459a6",
            Self::Orange => "#bd6100",
            Self::Purple => "#7846a6",
            Self::Red => "#b83232",
        }
    }
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Node {
    pub label: String,
    /// Optional emphasized suffix, such as a place capability.
    pub suffix: Option<String>,
    pub tooltip: String,
    pub shape: Shape,
    pub color: Color,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Hyperedge {
    pub sources: Vec<NodeId>,
    pub targets: Vec<NodeId>,
    pub label: String,
    pub tooltip: String,
    pub color: Color,
    pub dashed: bool,
    pub thick: bool,
}

impl Hyperedge {
    pub fn new(sources: Vec<NodeId>, targets: Vec<NodeId>, label: impl Into<String>) -> Self {
        Self {
            sources,
            targets,
            label: label.into(),
            tooltip: String::new(),
            color: Color::Black,
            dashed: false,
            thick: false,
        }
    }
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Hypergraph {
    pub nodes: Vec<Node>,
    pub edges: Vec<Hyperedge>,
}

impl Hypergraph {
    pub fn add_node(&mut self, node: Node) -> NodeId {
        let id = NodeId(self.nodes.len());
        self.nodes.push(node);
        id
    }

    pub fn layout(&self) -> Result<Drawing, LayoutError> {
        layout::layout(self)
    }

    pub fn to_svg(&self) -> Result<String, LayoutError> {
        let drawing = self.layout()?;
        Ok(svg::render(self, &drawing))
    }
}
