use std::io::{self};

use crate::{utils::HasCompilerCtxt, visualization::dot_graph::DotGraphWithEdgeCtxt};

use super::Graph;

pub struct GraphDrawer<T: io::Write> {
    dot_output: T,
    ctxt_output: Option<T>
}

impl<T: io::Write> GraphDrawer<T> {
    pub fn new(dot_output: T, ctxt_output: Option<T>) -> Self {
        Self { dot_output, ctxt_output }
    }

    pub(crate) fn draw<'a, 'tcx: 'a>(
        mut self,
        graph: Graph<'a>,
        ctxt: impl HasCompilerCtxt<'a, 'tcx>,
    ) -> io::Result<()> {
        let graph_with_edge_ctxt = DotGraphWithEdgeCtxt::from_graph(graph, ctxt);
        writeln!(self.dot_output, "{}", graph_with_edge_ctxt.graph)?;
        if let Some(ctxt_output) = self.ctxt_output {
            serde_json::to_writer_pretty(ctxt_output, &graph_with_edge_ctxt.edge_ctxt)?;

        }
        Ok(())
    }
}
