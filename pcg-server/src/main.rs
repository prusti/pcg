use axum::{
    Router,
    extract::Multipart,
    response::{Html, IntoResponse, Redirect, Response},
    routing::{get, post},
};
use hyper::StatusCode;
use std::{fs, net::SocketAddr, path::PathBuf};
use tokio::net::TcpListener;
use tower_http::services::ServeDir;
use tracing::{Level, debug, info};
use tracing_subscriber::FmtSubscriber;
use uuid::Uuid;

#[tokio::main]
async fn main() {
    // Initialize tracing with debug level
    FmtSubscriber::builder().with_max_level(Level::DEBUG).init();

    // Verify required JavaScript assets exist
    let required_assets = ["static/editor.bundle.js"];
    for asset in &required_assets {
        if !PathBuf::from(asset).exists() {
            eprintln!("ERROR: Required JavaScript asset not found: {}", asset);
            eprintln!(
                "Please build the assets by running 'npm install && npm run build' in the pcg-server directory."
            );
            std::process::exit(1);
        }
    }
    info!("All required JavaScript assets verified");

    // Ensure visualization storage directory exists
    // Use /data/vis in production (fly.dev mounted volume), fall back to ./vis-data for local development
    let vis_data_dir = std::env::var("VIS_DATA_DIR").unwrap_or_else(|_| "./vis-data".to_string());
    fs::create_dir_all(&vis_data_dir).expect("Failed to create visualization data directory");
    info!("Using visualization data directory: {}", vis_data_dir);

    let app = Router::new()
        .route("/", get(serve_upload_form))
        .route("/upload", post(handle_upload))
        .nest_service("/visualization", ServeDir::new("../visualization"))
        .nest_service("/vis-data", ServeDir::new(&vis_data_dir))
        .nest_service("/static", ServeDir::new("./static"));

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
        Err(e) => (StatusCode::INTERNAL_SERVER_ERROR, e).into_response(),
    }
}

// We call pcg-bin instead of using the PCG library directly so that we can
// capture all stdout/stderr output when compilation or analysis fails.
fn run_pcg_analysis(
    file_path: PathBuf,
    data_dir: PathBuf,
    use_polonius: bool,
) -> Result<(), String> {
    use std::process::Command;

    let pcg_bin_path = pcg_bin_utils::find_pcg_bin_for_server();

    info!(
        "Running PCG analysis using pcg-bin at: {} (polonius={})",
        pcg_bin_path.display(),
        use_polonius
    );

    let mut cmd = Command::new(&pcg_bin_path);
    cmd.arg(&file_path)
        .arg("--edition=2018")
        .env("PCG_VISUALIZATION", "true")
        .env("PCG_VISUALIZATION_DATA_DIR", &data_dir)
        .env("PCG_COUPLING", "true");

    if use_polonius {
        cmd.env("PCG_POLONIUS", "true");
    }

    let output = cmd
        .output()
        .map_err(|e| format!("Failed to execute pcg-bin at {}: {}", pcg_bin_path.display(), e))?;

    if !output.status.success() {
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let combined = format!(
            "PCG analysis failed:\n\n=== STDOUT ===\n{}\n\n=== STDERR ===\n{}",
            stdout, stderr
        );
        return Err(combined);
    }

    Ok(())
}

async fn handle_upload_inner(mut multipart: Multipart) -> Result<Response, String> {
    // Create a new directory with a unique name in the visualization data directory
    let vis_data_dir = std::env::var("VIS_DATA_DIR").unwrap_or_else(|_| "./vis-data".to_string());
    let base_dir = PathBuf::from(&vis_data_dir);
    let unique_dir = base_dir.join(Uuid::new_v4().to_string());
    fs::create_dir_all(&unique_dir).map_err(|e| e.to_string())?;
    debug!("Created visualization directory: {:?}", unique_dir);

    // Create data directory
    let data_dir = unique_dir.join("data");
    fs::create_dir(&data_dir).map_err(|e| e.to_string())?;

    // Debug all fields
    let mut code = String::new();
    let mut input_method = String::new();
    let mut borrow_checker = String::from("nll");

    while let Some(field) = multipart.next_field().await.map_err(|e| e.to_string())? {
        let name = field.name().ok_or("Field missing name")?.to_string();
        debug!("Processing multipart field: {}", name);

        match name.as_str() {
            "input-method" => {
                input_method = field.text().await.map_err(|e| e.to_string())?;
                debug!("Got input method: {}", input_method);
            }
            "borrow-checker" => {
                borrow_checker = field.text().await.map_err(|e| e.to_string())?;
                debug!("Got borrow checker: {}", borrow_checker);
            }
            "code" => {
                let code_text = field.text().await.map_err(|e| e.to_string())?;
                debug!("Got code field content length: {}", code_text.len());
                if input_method == "code" {
                    code = code_text;
                    debug!("Using code from textarea");
                } else {
                    debug!(
                        "Ignoring code field because input method is: {}",
                        input_method
                    );
                }
            }
            "file" => {
                debug!("Processing file field, input_method={}", input_method);
                if input_method == "file" {
                    let file_name = field.file_name().ok_or("No file name")?.to_string();
                    debug!("File name: {}", file_name);

                    if !file_name.ends_with(".rs") {
                        return Ok((
                            StatusCode::BAD_REQUEST,
                            "Only Rust files (.rs) are accepted",
                        )
                            .into_response());
                    }

                    let contents = field.bytes().await.map_err(|e| e.to_string())?;
                    code = String::from_utf8(contents.to_vec()).map_err(|e| e.to_string())?;
                    debug!("Extracted code from file, length: {}", code.len());
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

    debug!("Submitted Rust code:\n{}", code);

    fs::write(&file_path, &code).map_err(|e| e.to_string())?;

    let abs_file_path = file_path.canonicalize().map_err(|e| e.to_string())?;
    let abs_data_dir = data_dir.canonicalize().map_err(|e| e.to_string())?;
    info!("Using absolute file path: {:?}", abs_file_path);
    info!("Using absolute data dir: {:?}", abs_data_dir);

    // Run PCG analysis using pcg-bin
    let use_polonius = borrow_checker == "polonius";
    let result = run_pcg_analysis(abs_file_path, abs_data_dir, use_polonius);

    if let Err(e) = result {
        return Ok((StatusCode::INTERNAL_SERVER_ERROR, e.to_string()).into_response());
    }

    // Redirect to local visualization with data source URL
    let unique_dir_name = unique_dir.file_name().unwrap().to_str().unwrap();
    let redirect_url = format!("/visualization/?datasrc=/vis-data/{}", unique_dir_name);
    Ok(Redirect::to(&redirect_url).into_response())
}
