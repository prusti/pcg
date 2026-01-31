use serde_derive::{Deserialize, Serialize};

use crate::{
    rustc_interface::{hir::def_id::LocalDefId, middle::ty::TyCtxt},
    utils::data_structures::HashMap,
    visualization::mir_graph::SourcePos,
};
use std::path::PathBuf;

#[derive(Debug, Clone, Deserialize, Hash, PartialEq, Eq, Serialize)]
#[serde(transparent)]
pub(crate) struct FunctionSlug(PathBuf);

impl FunctionSlug {
    pub(crate) fn new(def_id: LocalDefId, tcx: TyCtxt<'_>) -> Self {
        let path: PathBuf = tcx.def_path_str(def_id.to_def_id()).into();
        Self(path)
    }

    pub(crate) fn path(&self) -> &PathBuf {
        &self.0
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, Deserialize, Serialize)]
#[cfg_attr(feature = "type-export", derive(specta::Type))]
pub(crate) struct FunctionMetadata {
    name: String,
    source: String,
    start: SourcePos,
}

impl FunctionMetadata {
    pub fn new(name: String, source: String, start: SourcePos) -> Self {
        Self {
            name,
            source,
            start,
        }
    }
}

#[derive(Default, Deserialize, Serialize)]
#[serde(transparent)]
pub(crate) struct FunctionsMetadata {
    functions: HashMap<FunctionSlug, FunctionMetadata>,
}

impl FunctionsMetadata {
    pub fn new() -> Self {
        Self {
            functions: HashMap::default(),
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.functions.is_empty()
    }

    pub fn insert(&mut self, slug: FunctionSlug, function: FunctionMetadata) {
        self.functions.insert(slug, function);
    }
}
