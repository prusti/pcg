use crate::{
    pcg::{DataflowStmtPhase, EvalStmtPhase, PcgArena, PcgEngine, PcgRef, ctxt::AnalysisCtxt},
    pcg_validity_assert,
    rustc_interface::{index::IndexVec, middle::mir},
    utils::{CompilerCtxt, StringOf, eval_stmt_data::EvalStmtData},
    visualization::write_pcg_dot_graph_to_file,
};
use derive_more::{Deref, From};
use serde_derive::Serialize;
use std::{
    cell::RefCell,
    fs::create_dir_all,
    path::{Path, PathBuf},
};

#[derive(Clone, Serialize, Debug, From, Deref)]
#[serde(transparent)]
#[cfg_attr(feature = "type-export", derive(specta::Type))]
pub(crate) struct PathToDotFile(PathBuf);

#[derive(Clone, Serialize, Debug)]
#[cfg_attr(feature = "type-export", derive(specta::Type))]
pub(crate) struct StmtGraphs<PhaseKey = StringOf<DataflowStmtPhase>> {
    at_phase: Vec<DotFileAtPhase<PhaseKey>>,
    actions: EvalStmtData<Vec<PathToDotFile>>,
}

#[derive(Clone, Serialize, Debug)]
#[cfg_attr(feature = "type-export", derive(specta::Type))]
pub(crate) struct DotFileAtPhase<PhaseKey> {
    phase: PhaseKey,
    filename: PathToDotFile,
}

impl<PhaseKey> DotFileAtPhase<PhaseKey> {
    pub(crate) fn new(phase: PhaseKey, filename: PathToDotFile) -> Self {
        Self { phase, filename }
    }
}

impl Default for StmtGraphs {
    fn default() -> Self {
        Self {
            at_phase: Vec::new(),
            actions: EvalStmtData::default(),
        }
    }
}

impl StmtGraphs {
    pub(crate) fn relative_filename(location: mir::Location, to_graph: ToGraph) -> PathToDotFile {
        let path_str = match to_graph {
            ToGraph::Phase(phase) => {
                format!(
                    "{:?}_stmt_{}_{}.dot",
                    location.block,
                    location.statement_index,
                    phase.to_filename_str_part()
                )
            }
            ToGraph::Action(phase, action_idx) => {
                format!(
                    "{:?}_stmt_{}_{:?}_action_{}.dot",
                    location.block, location.statement_index, phase, action_idx,
                )
            }
        };
        PathToDotFile(PathBuf::from(path_str))
    }

    pub(crate) fn insert_for_phase(&mut self, phase: DataflowStmtPhase, filename: PathToDotFile) {
        self.at_phase
            .push(DotFileAtPhase::new(StringOf::new_display(phase), filename));
    }

    pub(crate) fn insert_for_action(
        &mut self,
        phase: EvalStmtPhase,
        action_idx: usize,
        filename: PathToDotFile,
    ) {
        let within_phase = &mut self.actions[phase];
        assert_eq!(
            within_phase.len(),
            action_idx,
            "Action index {action_idx} isn't equal to number of existing actions for {phase:?}"
        );
        within_phase.push(filename);
    }
}

#[derive(Clone, Copy)]
pub(crate) enum ToGraph {
    Phase(DataflowStmtPhase),
    Action(EvalStmtPhase, usize),
}

fn dot_filename_for(output_dir: &Path, relative_filename: &PathToDotFile) -> PathBuf {
    output_dir.join(&relative_filename.0)
}

impl<'a, 'tcx: 'a> AnalysisCtxt<'a, 'tcx> {
    pub(crate) fn generate_pcg_debug_visualization_graph<'pcg>(
        self,
        location: mir::Location,
        to_graph: ToGraph,
        pcg: PcgRef<'pcg, 'tcx>,
    ) {
        if location.block.as_usize() == 0 {
            assert!(!matches!(
                to_graph,
                ToGraph::Phase(DataflowStmtPhase::Join(_))
            ));
        }
        if let Some(debug_data) = self.graphs {
            let relative_filename = StmtGraphs::relative_filename(location, to_graph);
            let filename = dot_filename_for(debug_data.dot_output_dir, &relative_filename);
            match to_graph {
                ToGraph::Action(phase, action_idx) => {
                    debug_data.dot_graphs.borrow_mut().insert_for_action(
                        location,
                        phase,
                        action_idx,
                        relative_filename,
                    );
                }
                ToGraph::Phase(phase) => debug_data.dot_graphs.borrow_mut().insert_for_phase(
                    location.statement_index,
                    phase,
                    relative_filename,
                ),
            }

            write_pcg_dot_graph_to_file(pcg, self.ctxt.as_dyn(), location, &filename).unwrap();
        }
    }
}

#[derive(Clone, Debug, Serialize)]
pub(crate) struct PcgDotGraphsForBlock {
    pub(crate) graphs: Vec<StmtGraphs>,
    #[serde(skip)]
    block: mir::BasicBlock,
}

impl PcgDotGraphsForBlock {
    pub(crate) fn new(block: mir::BasicBlock, ctxt: CompilerCtxt<'_, '_>) -> Self {
        let num_statements = ctxt.body().basic_blocks[block].statements.len();
        Self {
            block,
            graphs: vec![StmtGraphs::default(); num_statements + 1],
        }
    }

    pub(crate) fn insert_for_action(
        &mut self,
        location: mir::Location,
        phase: EvalStmtPhase,
        action_idx: usize,
        filename: PathToDotFile,
    ) {
        pcg_validity_assert!(location.block == self.block);
        self.graphs[location.statement_index].insert_for_action(phase, action_idx, filename);
    }

    pub(crate) fn insert_for_phase(
        &mut self,
        statement_index: usize,
        phase: DataflowStmtPhase,
        filename: PathToDotFile,
    ) {
        self.graphs[statement_index].insert_for_phase(phase, filename);
    }
}

#[derive(Copy, Clone, Debug)]
pub(crate) struct PcgBlockDebugVisualizationGraphs<'a> {
    #[allow(dead_code)]
    block: mir::BasicBlock,
    pub(crate) dot_output_dir: &'a Path,
    pub(crate) dot_graphs: &'a RefCell<PcgDotGraphsForBlock>,
}

impl<'a> PcgBlockDebugVisualizationGraphs<'a> {
    pub(crate) fn new(
        block: mir::BasicBlock,
        dot_output_dir: &'a Path,
        dot_graphs: &'a RefCell<PcgDotGraphsForBlock>,
    ) -> Self {
        Self {
            block,
            dot_output_dir,
            dot_graphs,
        }
    }
}

pub(crate) struct PcgEngineDebugData<'a> {
    debug_output_dir: &'a Path,
    dot_graphs: IndexVec<mir::BasicBlock, &'a RefCell<PcgDotGraphsForBlock>>,
}

impl<'a> PcgEngineDebugData<'a> {
    pub(crate) fn new(dir_path: PathBuf, arena: PcgArena<'a>, ctxt: CompilerCtxt<'a, '_>) -> Self {
        if dir_path.exists() {
            std::fs::remove_dir_all(&dir_path).expect("Failed to delete directory contents");
        }
        create_dir_all(&dir_path).expect("Failed to create directory for DOT files");
        let dot_graphs: IndexVec<mir::BasicBlock, &'a RefCell<PcgDotGraphsForBlock>> =
            IndexVec::from_fn_n(
                |b| {
                    let blocks: &'a RefCell<PcgDotGraphsForBlock> =
                        arena.alloc(RefCell::new(PcgDotGraphsForBlock::new(b, ctxt)));
                    blocks
                },
                ctxt.body().basic_blocks.len(),
            );
        PcgEngineDebugData {
            debug_output_dir: arena.alloc(dir_path),
            dot_graphs,
        }
    }
}

impl<'a, 'tcx: 'a> PcgEngine<'a, 'tcx> {
    pub(crate) fn dot_graphs(
        &self,
        block: mir::BasicBlock,
    ) -> Option<PcgBlockDebugVisualizationGraphs<'a>> {
        self.debug_graphs.as_ref().map(|data| {
            PcgBlockDebugVisualizationGraphs::new(
                block,
                data.debug_output_dir,
                data.dot_graphs[block],
            )
        })
    }
}
