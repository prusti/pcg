use std::path::PathBuf;

use crate::{
    PcgCtxt, PcgCtxtCreator,
    utils::CompilerCtxt,
    visualization::{
        functions_metadata::{FunctionMetadata, FunctionSlug},
        mir_graph::SourcePos,
    },
};

impl<'a, 'tcx, T> CompilerCtxt<'a, 'tcx, T> {
    pub(crate) fn function_metadata_slug(&self) -> FunctionSlug {
        FunctionSlug::new(self.def_id(), self.tcx)
    }

    pub(crate) fn function_metadata(&self) -> FunctionMetadata {
        let start = SourcePos::new(self.mir.span.lo(), self.tcx);
        FunctionMetadata::new(
            self.body_def_path_str().into(),
            self.source().unwrap(),
            start,
        )
    }
}

impl<'a, 'tcx> PcgCtxt<'a, 'tcx> {
    pub fn update_debug_visualization_metadata(&self) {
        if let Some(metadata) = self.visualization_function_metadata() {
            self.settings.write_new_debug_visualization_metadata(
                self.compiler_ctxt.function_metadata_slug(),
                &metadata,
            );
        }
    }

    pub(crate) fn visualization_function_metadata(&self) -> Option<FunctionMetadata> {
        if self.settings.visualization {
            Some(self.compiler_ctxt.function_metadata())
        } else {
            None
        }
    }

    pub fn visualization_output_path(&self) -> Option<PathBuf> {
        if self.settings.visualization {
            Some(
                self.settings
                    .visualization_data_dir
                    .join(self.compiler_ctxt.function_metadata_slug().path()),
            )
        } else {
            None
        }
    }
}

impl<'tcx> PcgCtxtCreator<'tcx> {
    pub fn write_debug_visualization_metadata(self) {
        let metadata = self.debug_function_metadata.take();
        if !metadata.is_empty() {
            self.settings.write_functions_json(&metadata);
        }
    }
}
