use crate::{
    PcgCtxt,
    action::AppliedActionDebugRepr,
    results::PcgAnalysisResults,
    rustc_interface::middle::mir,
    utils::{DebugRepr, HasCompilerCtxt, eval_stmt_data::EvalStmtData, mir::BasicBlock},
};
use crate::{
    action::PcgActionDebugRepr,
    visualization::stmt_graphs::{PcgLoopDebugData, StmtGraphs},
};
use serde_derive::Serialize;

#[derive(Serialize)]
#[cfg_attr(feature = "type-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "type-export", ts(export))]
pub(crate) struct PcgBlockVisualizationData {
    statements: Vec<PcgStmtVisualizationData>,
    successors: std::collections::HashMap<BasicBlock, PcgSuccessorVisualizationData>,
    loop_data: Option<PcgLoopDebugData>,
}

#[derive(Serialize)]
#[cfg_attr(feature = "type-export", derive(ts_rs::TS))]
#[cfg_attr(feature = "type-export", ts(export))]
pub(crate) struct PcgVisualizationData(
    std::collections::HashMap<BasicBlock, PcgBlockVisualizationData>,
);

impl PcgVisualizationData {
    pub(crate) fn new() -> Self {
        Self(std::collections::HashMap::new())
    }

    pub(crate) fn insert(&mut self, block: BasicBlock, data: PcgBlockVisualizationData) {
        self.0.insert(block, data);
    }

    pub(crate) fn from_analysis_results<'a, 'tcx: 'a>(
        analysis_results: &mut PcgAnalysisResults<'a, 'tcx>,
        pcg_ctxt: &'a PcgCtxt<'_, 'tcx>,
    ) -> Self {
        let mut visualization_data = PcgVisualizationData::new();
        for block in pcg_ctxt.body().basic_blocks.indices() {
            use crate::visualization::data::PcgBlockVisualizationData;

            let Ok(Some(pcg_block)) = analysis_results.get_all_for_bb(block) else {
                continue;
            };
            let ctxt = analysis_results.analysis().analysis_ctxt(block);
            let (loop_data, debug_graphs) = if let Some(data) = ctxt.visualization_data {
                let block_data = data.block_data.borrow();
                (block_data.loop_data.clone(), block_data.graphs.clone())
            } else {
                (None, Vec::new())
            };

            let statements = pcg_block
                .statements()
                .map(|stmt| {
                    use crate::visualization::data::PcgStmtVisualizationData;

                    let actions: EvalStmtData<Vec<AppliedActionDebugRepr>> =
                        stmt.actions.debug_repr(pcg_ctxt.compiler_ctxt);
                    PcgStmtVisualizationData {
                        actions,
                        graphs: debug_graphs
                            .get(stmt.location.statement_index)
                            .cloned()
                            .unwrap_or_default(),
                    }
                })
                .collect();

            let successors = pcg_block
                .successors()
                .map(|succ| {
                    use crate::visualization::data::PcgSuccessorVisualizationData;

                    (
                        succ.block().into(),
                        PcgSuccessorVisualizationData {
                            actions: succ.actions().debug_repr(pcg_ctxt.compiler_ctxt),
                        },
                    )
                })
                .collect();

            visualization_data.insert(
                block.into(),
                PcgBlockVisualizationData {
                    statements,
                    successors,
                    loop_data,
                },
            );
        }
        visualization_data
    }
}

#[derive(Serialize)]
#[cfg_attr(feature = "type-export", derive(ts_rs::TS))]
pub(crate) struct PcgStmtVisualizationData {
    pub(crate) actions: EvalStmtData<Vec<AppliedActionDebugRepr>>,
    pub(crate) graphs: StmtGraphs,
}

#[derive(Serialize)]
#[cfg_attr(feature = "type-export", derive(ts_rs::TS))]
pub(crate) struct PcgSuccessorVisualizationData {
    pub(crate) actions: Vec<PcgActionDebugRepr>,
}
