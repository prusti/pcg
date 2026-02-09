#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;

use std::{fs, io, path::{Path, PathBuf}, sync::Arc};

use borrowck_body_storage::{set_mir_borrowck, take_stored_body};
use pcg::{
    PcgCtxtCreator,
    borrow_checker::r#impl::PoloniusBorrowChecker,
    results::PcgAnalysisResults,
    run_pcg,
    rustc_interface::{
        driver::{self, Compilation},
        hir::def::DefKind,
        interface::{Config, interface::Compiler},
        middle::ty::TyCtxt,
        span::source_map::FileLoader,
    },
    utils::callbacks::{RustBorrowCheckerImpl, in_cargo_crate},
};

use pcg::rustc_interface::driver::run_compiler;

pub struct StringLoader(pub String);

impl FileLoader for StringLoader {
    fn file_exists(&self, _: &Path) -> bool {
        true
    }

    fn read_file(&self, _: &Path) -> io::Result<String> {
        Ok(self.0.clone())
    }

    fn read_binary_file(&self, path: &Path) -> io::Result<Arc<[u8]>> {
        Ok(fs::read(path)?.into())
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        std::env::current_dir()
    }
}

type TestCallback = dyn for<'a, 'tcx> Fn(PcgAnalysisResults<'a, 'tcx>) + Send + Sync + 'static;

struct TestCallbacks {
    input: String,
    callback: Option<Box<TestCallback>>,
}

impl driver::Callbacks for TestCallbacks {
    fn config(&mut self, config: &mut Config) {
        assert!(config.override_queries.is_none());
        config.override_queries = Some(set_mir_borrowck);
        config.file_loader = Some(Box::new(StringLoader(self.input.clone())));
    }

    fn after_analysis(&mut self, _compiler: &Compiler, tcx: TyCtxt<'_>) -> Compilation {
        tracing::info!("after_analysis");
        unsafe {
            run_pcg_on_first_fn(tcx, self.callback.take().unwrap());
        }
        if in_cargo_crate() {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }
}

/// # Safety
///
/// Stored bodies must come from the same `tcx`.
unsafe fn run_pcg_on_first_fn<'tcx>(
    tcx: TyCtxt<'tcx>,
    callback: impl for<'mir, 'arena> Fn(PcgAnalysisResults<'mir, 'tcx>) + Send + Sync + 'static,
) {
    let def_id = tcx
        .hir_body_owners()
        .find(|def_id| matches!(tcx.def_kind(*def_id), DefKind::Fn | DefKind::AssocFn))
        .unwrap();
    let body = unsafe { take_stored_body(tcx, def_id) };
    let ctxt_creator = PcgCtxtCreator::new(tcx);
    let bc = RustBorrowCheckerImpl::Polonius(PoloniusBorrowChecker::new(tcx, &body));
    let pcg_ctxt = ctxt_creator.new_ctxt(&body, &bc);
    let output = run_pcg(pcg_ctxt);
    callback(output);
}

pub fn run_pcg_on_str(
    input: &str,
    callback: impl for<'mir, 'tcx> Fn(PcgAnalysisResults<'mir, 'tcx>) + Send + Sync + 'static,
) {
    run_compiler(
        &[
            "rustc".to_string(),
            "dummy.rs".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
        ],
        &mut TestCallbacks {
            input: input.to_string(),
            callback: Some(Box::new(callback)),
        },
    );
}
