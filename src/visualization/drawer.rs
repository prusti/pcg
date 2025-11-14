use std::io::{self};

use crate::{utils::HasCompilerCtxt, visualization::dot_graph::DotGraph};

use super::{Graph, GraphDrawer};

impl<T: io::Write> GraphDrawer<T> {
    pub fn new(out: T) -> Self {
        Self { out }
    }

    pub(crate) fn draw<'a, 'tcx: 'a>(
        mut self,
        graph: Graph<'a>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> io::Result<()> {
        let dot_graph = DotGraph {
            name: "CapabilitySummary".into(),
            nodes: graph.nodes.iter().map(|g| g.to_dot_node()).collect(),
            edges: graph
                .edges
                .into_iter()
                .enumerate()
                .map(|(i, e)| e.to_dot_edge(Some(i), ctxt))
                .collect(),
        };
        writeln!(self.out, "{dot_graph}")
    }
}
