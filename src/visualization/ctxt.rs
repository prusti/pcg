use crate::{
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
