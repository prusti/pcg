use std::path::PathBuf;

use crate::{
    PcgCtxt, PcgCtxtCreator,
    utils::CompilerCtxt,
    visualization::{
        functions_metadata::{FunctionMetadata, FunctionSlug},
        mir_graph::SourcePos,
    },
};

impl<T> CompilerCtxt<'_, '_, T> {
    pub(crate) fn function_metadata_slug(&self) -> FunctionSlug {
        FunctionSlug::new(self.def_id(), self.tcx)
    }

    pub(crate) fn function_metadata(&self) -> FunctionMetadata {
        let start = SourcePos::new(self.mir.span.lo(), self.tcx);
        let def_id = self.def_id();
        let fn_sig = self.tcx.fn_sig(def_id).instantiate_identity();
        let fn_sig = self.tcx.liberate_late_bound_regions(def_id.into(), fn_sig);
        let signature = format!("{fn_sig}");
        let debug_signature = format!("{fn_sig:#?}");
        FunctionMetadata::new(
            self.body_def_path_str(),
            signature,
            debug_signature,
            self.source().unwrap(),
            start,
        )
    }
}

impl PcgCtxt<'_, '_> {
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

impl PcgCtxtCreator<'_> {
    pub fn write_debug_visualization_metadata(self) {
        let metadata = self.debug_function_metadata.take();
        if !metadata.is_empty() {
            self.settings.write_functions_json(&metadata);
        }
    }
}
