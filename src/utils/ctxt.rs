use crate::{
    borrow_checker::BorrowCheckerInterface,
    rustc_interface::{
        RustBitSet,
        middle::{
            mir::{BasicBlock, Body, HasLocalDecls, Local, VarDebugInfoContents},
            ty::TyCtxt,
        },
        mir_dataflow,
        span::{SpanSnippetError, def_id::LocalDefId},
    },
    utils::{HasBorrowCheckerCtxt, HasCompilerCtxt, HasTyCtxt, Place},
    visualization::functions_metadata::{FunctionMetadata, FunctionSlug},
};

#[derive(Copy, Clone)]
pub struct CompilerCtxt<'a, 'tcx, T = &'a dyn BorrowCheckerInterface<'tcx>> {
    pub(crate) mir: &'a Body<'tcx>,
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) bc: T,
}

impl<'a, 'tcx> HasTyCtxt<'tcx> for CompilerCtxt<'a, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
}

impl<T: Copy> std::fmt::Debug for CompilerCtxt<'_, '_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "CompilerCtxt",)
    }
}

impl<'a, 'tcx, T: BorrowCheckerInterface<'tcx> + ?Sized> CompilerCtxt<'a, 'tcx, &'a T> {
    pub fn as_dyn(self) -> CompilerCtxt<'a, 'tcx, &'a dyn BorrowCheckerInterface<'tcx>> {
        CompilerCtxt {
            mir: self.mir,
            tcx: self.tcx(),
            bc: self.bc.as_dyn(),
        }
    }
}

impl<'a, 'tcx, T> CompilerCtxt<'a, 'tcx, T> {
    pub fn new(mir: &'a Body<'tcx>, tcx: TyCtxt<'tcx>, bc: T) -> Self {
        Self { mir, tcx, bc }
    }

    pub fn body(self) -> &'a Body<'tcx> {
        self.mir
    }

    pub fn tcx(self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn source(&self) -> Result<String, SpanSnippetError> {
        let source_map = self.tcx.sess.source_map();
        let span = self.mir.span;
        source_map.span_to_snippet(span)
    }

    pub fn source_lines(&self) -> Result<Vec<String>, SpanSnippetError> {
        let source = self.source()?;
        Ok(source.lines().map(|l| l.to_string()).collect::<Vec<_>>())
    }

    pub fn bc(&self) -> T
    where
        T: Copy,
    {
        self.bc
    }

    pub fn body_def_path_str(&self) -> String {
        self.tcx.def_path_str(self.def_id())
    }

    pub fn local_place(&self, var_name: &str) -> Option<Place<'tcx>> {
        for info in &self.mir.var_debug_info {
            if let VarDebugInfoContents::Place(place) = info.value
                && info.name.to_string() == var_name
            {
                return Some(place.into());
            }
        }
        None
    }

    pub(crate) fn def_id(&self) -> LocalDefId {
        self.mir.source.def_id().expect_local()
    }

    pub(crate) fn function_metadata_slug(&self) -> FunctionSlug {
        FunctionSlug::new(self.def_id(), self.tcx)
    }

    pub(crate) fn function_metadata(&self) -> FunctionMetadata {
        FunctionMetadata::new(self.body_def_path_str().into(), self.source().unwrap())
    }
}

impl CompilerCtxt<'_, '_> {
    /// Returns `true` iff the edge from `from` to `to` is a back edge (i.e.
    /// `to` dominates `from`).
    pub(crate) fn is_back_edge(&self, from: BasicBlock, to: BasicBlock) -> bool {
        self.mir.basic_blocks.dominators().dominates(to, from)
    }

    pub fn num_args(self) -> usize {
        self.mir.arg_count
    }

    pub fn local_count(self) -> usize {
        self.mir.local_decls().len()
    }

    pub fn always_live_locals(self) -> RustBitSet<Local> {
        mir_dataflow::impls::always_storage_live_locals(self.mir)
    }

    pub fn always_live_locals_non_args(self) -> RustBitSet<Local> {
        let mut all = self.always_live_locals();
        for arg in 0..self.mir.arg_count + 1 {
            // Includes `RETURN_PLACE`
            all.remove(arg.into());
        }
        all
    }
}

impl<'a, 'tcx, T: Copy> HasCompilerCtxt<'a, 'tcx> for CompilerCtxt<'a, 'tcx, T> {
    fn ctxt(self) -> CompilerCtxt<'a, 'tcx, ()> {
        CompilerCtxt::new(self.mir, self.tcx, ())
    }

    fn body(self) -> &'a Body<'tcx> {
        self.mir
    }

    fn tcx(self) -> TyCtxt<'tcx> {
        self.tcx
    }
}

impl<'a, 'tcx, T: Copy> HasBorrowCheckerCtxt<'a, 'tcx, T> for CompilerCtxt<'a, 'tcx, T> {
    fn bc(&self) -> T {
        self.bc
    }

    fn bc_ctxt(&self) -> CompilerCtxt<'a, 'tcx, T> {
        *self
    }
}
