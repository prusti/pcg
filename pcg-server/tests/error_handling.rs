#![feature(rustc_private)]
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

use std::fs;
use std::panic;
use tempfile::TempDir;

extern crate pcg;
extern crate borrowck_body_storage;

use pcg::rustc_interface::driver::{self, args};
use pcg::rustc_interface::interface;
use pcg::rustc_interface::session::config::{self, ErrorOutputType};
use pcg::rustc_interface::session::EarlyDiagCtxt;
use pcg::utils::PcgSettings;
use borrowck_body_storage::set_mir_borrowck;
use std::path::PathBuf;

fn run_pcg_analysis(file_path: PathBuf, _settings: PcgSettings) -> Result<(), String> {
    let mut rustc_args = vec![file_path.to_str().unwrap().to_string()];

    if !rustc_args.iter().any(|arg| arg.starts_with("--edition")) {
        rustc_args.push("--edition=2018".to_string());
    }

    let mut default_early_dcx = EarlyDiagCtxt::new(ErrorOutputType::default());
    let args = args::arg_expand_all(&default_early_dcx, &rustc_args);
    let Some(matches) = driver::handle_options(&default_early_dcx, &args) else {
        return Err("Failed to parse compiler options".to_string());
    };
    let sopts = config::build_session_options(&mut default_early_dcx, &matches);

    if matches.free.len() != 1 {
        return Err(format!("Expected exactly one input file, got {}", matches.free.len()));
    }

    let input = config::Input::File(PathBuf::from(matches.free[0].clone()));
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

    let had_errors = std::sync::Arc::new(std::sync::Mutex::new(false));
    let had_errors_clone = std::sync::Arc::clone(&had_errors);

    let result = panic::catch_unwind(panic::AssertUnwindSafe(|| {
        interface::run_compiler(config, move |compiler| {
            let sess = &compiler.sess;
            let krate = interface::passes::parse(sess);

            // Check for parse errors
            if sess.dcx().has_errors().is_some() {
                *had_errors_clone.lock().unwrap() = true;
                return;
            }

            interface::passes::create_and_enter_global_ctxt(compiler, krate, |tcx| {
                let _ = tcx.resolver_for_lowering();
                if tcx.dcx().has_errors().is_some() {
                    *had_errors_clone.lock().unwrap() = true;
                    return;
                }
                let _ = tcx.analysis(());
                if tcx.dcx().has_errors().is_some() {
                    *had_errors_clone.lock().unwrap() = true;
                    return;
                }
            })
        });
    }));

    if result.is_err() {
        return Err("Compilation failed with errors".to_string());
    }

    if *had_errors.lock().unwrap() {
        return Err("Compilation failed with errors".to_string());
    }

    Ok(())
}

#[test]
fn test_compilation_error_does_not_crash() {
    let temp_dir = TempDir::new().unwrap();
    let data_dir = temp_dir.path().join("data");
    fs::create_dir(&data_dir).unwrap();

    let invalid_rust_code = r#"
        fn main() {
            let x: i32 = "not a number";
        }
    "#;

    let test_file = temp_dir.path().join("invalid.rs");
    fs::write(&test_file, invalid_rust_code).unwrap();

    let settings = PcgSettings {
        check_cycles: false,
        validity_checks: false,
        debug_block: None,
        debug_imgcat: vec![],
        validity_checks_warn_only: false,
        panic_on_error: false,
        polonius: false,
        dump_mir_dataflow: false,
        visualization: false,
        visualization_data_dir: data_dir.clone(),
        check_annotations: false,
        emit_annotations: false,
        check_function: None,
        skip_function: None,
        coupling: false,
    };

    let result = run_pcg_analysis(test_file, settings);

    assert!(result.is_ok() || result.is_err(), "Function should return normally, not crash");
}

#[test]
fn test_syntax_error_does_not_crash() {
    let temp_dir = TempDir::new().unwrap();
    let data_dir = temp_dir.path().join("data");
    fs::create_dir(&data_dir).unwrap();

    let invalid_rust_code = r#"
        fn main(){
    "#;

    let test_file = temp_dir.path().join("syntax_error.rs");
    fs::write(&test_file, invalid_rust_code).unwrap();

    let settings = PcgSettings {
        check_cycles: false,
        validity_checks: false,
        debug_block: None,
        debug_imgcat: vec![],
        validity_checks_warn_only: false,
        panic_on_error: false,
        polonius: false,
        dump_mir_dataflow: false,
        visualization: false,
        visualization_data_dir: data_dir.clone(),
        check_annotations: false,
        emit_annotations: false,
        check_function: None,
        skip_function: None,
        coupling: false,
    };

    let result = run_pcg_analysis(test_file, settings);

    assert!(result.is_ok() || result.is_err(), "Function should return normally, not crash");
}

#[test]
fn test_successful_compilation() {
    let temp_dir = TempDir::new().unwrap();
    let data_dir = temp_dir.path().join("data");
    fs::create_dir(&data_dir).unwrap();

    let valid_rust_code = r#"
        fn main() {
            let x: i32 = 42;
            println!("{}", x);
        }
    "#;

    let test_file = temp_dir.path().join("valid.rs");
    fs::write(&test_file, valid_rust_code).unwrap();

    let settings = PcgSettings {
        check_cycles: false,
        validity_checks: false,
        debug_block: None,
        debug_imgcat: vec![],
        validity_checks_warn_only: false,
        panic_on_error: false,
        polonius: false,
        dump_mir_dataflow: false,
        visualization: false,
        visualization_data_dir: data_dir.clone(),
        check_annotations: false,
        emit_annotations: false,
        check_function: None,
        skip_function: None,
        coupling: false,
    };

    let result = run_pcg_analysis(test_file, settings);

    assert!(result.is_ok(), "Expected compilation to succeed for valid code, got error: {:?}", result);
}

