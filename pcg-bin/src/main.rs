#![feature(rustc_private)]
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

mod callbacks;

use borrowck_body_storage::set_mir_borrowck;

use pcg::rustc_interface::driver::{self, args};
use pcg::rustc_interface::interface;
use pcg::rustc_interface::session::EarlyDiagCtxt;
use pcg::rustc_interface::session::config::{self, ErrorOutputType};
use pcg::utils::{GLOBAL_SETTINGS, SETTINGS};

use crate::callbacks::PcgAsRustcCallbacks;

fn init_tracing() {
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .with_writer(std::io::stderr)
        .init();
}

fn main() {
    init_tracing();
    let mut rustc_args = std::env::args().skip(1).collect::<Vec<_>>();

    if !rustc_args.iter().any(|arg| arg.starts_with("--edition")) {
        rustc_args.push("--edition=2018".to_string());
    }

    if SETTINGS.polonius {
        rustc_args.push("-Zpolonius".to_string());
    }

    if GLOBAL_SETTINGS.allow_borrowck_errors {
        borrowck_body_storage::allow_borrowck_errors();
    }

    if GLOBAL_SETTINGS.be_rustc {
        // Behaves exactly like rustc, but also runs PCG on all functions
        let mut args = vec!["rustc".to_string()];
        args.extend(rustc_args);
        driver::run_compiler(&args, &mut PcgAsRustcCallbacks);
        return;
    }
    let mut default_early_dcx = EarlyDiagCtxt::new(ErrorOutputType::default());
    let args = args::arg_expand_all(&default_early_dcx, &rustc_args);
    let Some(matches) = driver::handle_options(&default_early_dcx, &args) else {
        return;
    };
    let sopts = config::build_session_options(&mut default_early_dcx, &matches);
    assert!(matches.free.len() == 1, "Expected exactly one input file");
    let input = config::Input::File(std::path::PathBuf::from(matches.free[0].clone()));
    let config = interface::Config {
        opts: sopts,
        crate_cfg: vec![],
        crate_check_cfg: vec![],
        input,
        output_file: None,
        output_dir: None,
        ice_file: None,
        file_loader: None,
        locale_resources: driver::DEFAULT_LOCALE_RESOURCES.to_vec(),
        lint_caps: Default::default(),
        psess_created: None,
        hash_untracked_state: None,
        register_lints: None,
        override_queries: Some(set_mir_borrowck),
        extra_symbols: vec![],
        make_codegen_backend: None,
        registry: driver::diagnostics_registry(),
        using_internal_features: &driver::USING_INTERNAL_FEATURES,
        expanded_args: args,
    };
    interface::run_compiler(config, |compiler| {
        let sess = &compiler.sess;
        let krate = interface::passes::parse(sess);
        interface::passes::create_and_enter_global_ctxt(compiler, krate, |tcx| {
            // Make sure name resolution and macro expansion is run.
            let _ = tcx.resolver_for_lowering();
            tcx.dcx().abort_if_errors();
            let _ = tcx.ensure_ok().analysis(());
            // Safety: `config` has `override_queries` set to [`set_mir_borrowck`], and the `tcx`
            // is the same `tcx` where the borrow-checking occurred.
            unsafe {
                eprintln!("Running PCG on all functions");
                callbacks::run_pcg_on_all_fns(tcx);
            }
        })
    })
}
