#![feature(rustc_private)]
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

use axum::{
    extract::Multipart,
    response::{Html, IntoResponse, Redirect, Response},
    routing::{get, post},
    Router,
};
use hyper::StatusCode;
use std::{backtrace::Backtrace, fs, io::Write, net::SocketAddr, path::PathBuf};
use tokio::net::TcpListener;
use tower_http::services::ServeDir;
use tracing::{debug, info, Level};
use tracing_subscriber::FmtSubscriber;
use uuid::Uuid;

use borrowck_body_storage::set_mir_borrowck;
use pcg::rustc_interface::driver::{self, args};
use pcg::rustc_interface::interface;
use pcg::rustc_interface::session::config::{self, ErrorOutputType};
use pcg::rustc_interface::session::EarlyDiagCtxt;

mod callbacks;
use callbacks::run_pcg_on_all_fns;

#[tokio::main]
async fn main() {
    // Initialize tracing with debug level
    FmtSubscriber::builder().with_max_level(Level::DEBUG).init();

    // Ensure tmp directory exists
    fs::create_dir_all("tmp").expect("Failed to create tmp directory");

    let app = Router::new()
        .route("/", get(serve_upload_form))
        .route("/upload", post(handle_upload))
        .fallback_service(ServeDir::new("./").append_index_html_on_directories(false));

    info!("Starting server on 0.0.0.0:4000");
    let addr = SocketAddr::from(([0, 0, 0, 0], 4000));
    let listener = TcpListener::bind(addr).await.unwrap();
    axum::serve(listener, app).await.unwrap();
}

async fn serve_upload_form() -> impl IntoResponse {
    let html_content =
        fs::read_to_string("templates/index.html").expect("Failed to read upload form template");
    Html(html_content)
}

async fn handle_upload(multipart: Multipart) -> Response {
    match handle_upload_inner(multipart).await {
        Ok(response) => response,
        Err(e) => {
            let backtrace = Backtrace::capture();
            let error_with_trace = format!("Error: {}\n\nBacktrace:\n{}", e, backtrace);
            (StatusCode::INTERNAL_SERVER_ERROR, error_with_trace).into_response()
        }
    }
}


fn run_pcg_analysis(file_path: PathBuf) -> Result<(), String> {
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

    interface::run_compiler(config, |compiler| {
        let sess = &compiler.sess;
        let krate = interface::passes::parse(sess);
        interface::passes::create_and_enter_global_ctxt(compiler, krate, |tcx| {
            let _ = tcx.resolver_for_lowering();
            tcx.dcx().abort_if_errors();
            let _ = tcx.ensure_ok().analysis(());
            unsafe {
                run_pcg_on_all_fns(tcx);
            }
        })
    });

    Ok(())
}

fn find_pcg_visualization_dir() -> Result<PathBuf, String> {
    let to_try = vec![
        PathBuf::from("visualization"),
        PathBuf::from("../visualization"),
    ];

    for path in to_try {
        if path.exists() {
            tracing::info!("Found visualization directory at {:?}", path);
            return Ok(path);
        }
    }

    Err("visualization directory not found".to_string())
}

async fn handle_upload_inner(mut multipart: Multipart) -> Result<Response, String> {
    // Create a new directory in ./tmp with a unique name
    let tmp_dir = PathBuf::from("tmp");
    let unique_dir = tmp_dir.join(Uuid::new_v4().to_string());
    fs::create_dir_all(&unique_dir).map_err(|e| e.to_string())?;
    debug!("Created temporary directory: {:?}", unique_dir);

    // Create data directory
    let data_dir = unique_dir.join("data");
    fs::create_dir(&data_dir).map_err(|e| e.to_string())?;

    // Debug all fields
    let mut code = String::new();
    let mut input_method = String::new();

    while let Some(field) = multipart.next_field().await.map_err(|e| e.to_string())? {
        let name = field.name().ok_or("Field missing name")?.to_string();
        debug!("Processing multipart field: {}", name);

        match name.as_str() {
            "input_method" => {
                input_method = field.text().await.map_err(|e| e.to_string())?;
                debug!("Got input method: {}", input_method);
            }
            "code" => {
                code = field.text().await.map_err(|e| e.to_string())?;
                debug!("Got code field content length: {}", code.len());
            }
            "file" => {
                if input_method == "file" {
                    let file_name = field.file_name().ok_or("No file name")?.to_string();

                    if !file_name.ends_with(".rs") {
                        return Ok((
                            StatusCode::BAD_REQUEST,
                            "Only Rust files (.rs) are accepted",
                        )
                            .into_response());
                    }

                    let contents = field.bytes().await.map_err(|e| e.to_string())?;
                    code = String::from_utf8(contents.to_vec()).map_err(|e| e.to_string())?;
                }
            }
            _ => {
                debug!("Unexpected field name: {}", name);
            }
        }
    }

    if code.is_empty() {
        return Ok((StatusCode::BAD_REQUEST, "No code content provided").into_response());
    }

    let file_path = unique_dir.join("input.rs");

    // Debug: Print the submitted code
    debug!("Submitted Rust code:\n{}", code);

    // Write the code to file
    fs::write(&file_path, &code).map_err(|e| e.to_string())?;

    // Debug: Verify file contents
    let saved_contents = fs::read_to_string(&file_path).map_err(|e| e.to_string())?;
    debug!("Saved file contents:\n{}", saved_contents);

    // Get absolute paths for both input file and data directory
    let abs_file_path = file_path.canonicalize().map_err(|e| e.to_string())?;
    let abs_data_dir = data_dir.canonicalize().map_err(|e| e.to_string())?;
    debug!("Using absolute file path: {:?}", abs_file_path);
    debug!("Using absolute data dir: {:?}", abs_data_dir);

    // Run PCG analysis using the library directly
    std::env::set_var("PCG_VISUALIZATION", "true");
    std::env::set_var("PCG_VISUALIZATION_DATA_DIR", abs_data_dir.to_str().unwrap());

    let result = run_pcg_analysis(abs_file_path);

    if let Err(e) = result {
        let error_message = format!("PCG analysis failed: {}", e);
        return Ok((StatusCode::INTERNAL_SERVER_ERROR, error_message).into_response());
    }

    let visualization_dir = find_pcg_visualization_dir()?;

    // Copy visualization files
    copy_dir(visualization_dir.join("dist"), unique_dir.join("dist")).map_err(|e| e.to_string())?;

    fs::copy(
        visualization_dir.join("index.html"),
        unique_dir.join("index.html"),
    )
    .map_err(|e| e.to_string())?;

    // Redirect to the visualization
    let redirect_path = format!(
        "/tmp/{}/index.html",
        unique_dir.file_name().unwrap().to_str().unwrap()
    );
    Ok(Redirect::to(&redirect_path).into_response())
}

fn copy_dir(src: PathBuf, dst: PathBuf) -> std::io::Result<()> {
    if !dst.exists() {
        fs::create_dir(&dst)?;
    }

    for entry in fs::read_dir(src)? {
        let entry = entry?;
        let ty = entry.file_type()?;
        let dst_path = dst.join(entry.file_name());

        if ty.is_dir() {
            copy_dir(entry.path(), dst_path)?;
        } else {
            fs::copy(entry.path(), dst_path)?;
        }
    }

    Ok(())
}
