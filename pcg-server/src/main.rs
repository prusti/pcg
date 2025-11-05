use axum::{
    extract::Multipart,
    response::{Html, IntoResponse, Redirect, Response},
    routing::{get, post},
    Router,
};
use hyper::StatusCode;
use std::{fs, net::SocketAddr, path::PathBuf};
use tokio::net::TcpListener;
use tower_http::services::ServeDir;
use tracing::{debug, info, Level};
use tracing_subscriber::FmtSubscriber;
use uuid::Uuid;

#[tokio::main]
async fn main() {
    // Initialize tracing with debug level
    FmtSubscriber::builder().with_max_level(Level::DEBUG).init();

    // Ensure tmp directory exists
    fs::create_dir_all("tmp").expect("Failed to create tmp directory");

    let app = Router::new()
        .route("/", get(serve_upload_form))
        .route("/upload", post(handle_upload))
        .nest_service("/visualization", ServeDir::new("../visualization"))
        .nest_service("/tmp", ServeDir::new("./tmp"))
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
fn run_pcg_analysis(file_path: PathBuf, data_dir: PathBuf) -> Result<(), String> {
    use std::process::Command;

    // Determine the path to the pcg_bin executable
    // In development: ../pcg-bin/target/release/pcg_bin (pcg-bin has its own workspace)
    // In Docker: ../target/release/pcg_bin (built in shared workspace)
    let pcg_bin_path = std::env::var("PCG_BIN_PATH")
        .unwrap_or_else(|_| {
            // Try development path first, fall back to Docker path
            let dev_path = "../pcg-bin/target/release/pcg_bin";
            let docker_path = "../target/release/pcg_bin";
            if std::path::Path::new(dev_path).exists() {
                dev_path.to_string()
            } else {
                docker_path.to_string()
            }
        });

    info!("Running PCG analysis using pcg-bin at: {}", pcg_bin_path);

    let output = Command::new(&pcg_bin_path)
        .arg(&file_path)
        .arg("--edition=2018")
        .env("PCG_VISUALIZATION", "true")
        .env("PCG_VISUALIZATION_DATA_DIR", &data_dir)
        .env("PCG_COUPLING", "true")
        .output()
        .map_err(|e| format!("Failed to execute pcg-bin at {}: {}", pcg_bin_path, e))?;

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

fn zip_directory(src_dir: &PathBuf, dst_file: &PathBuf) -> Result<(), String> {
    let file = fs::File::create(dst_file).map_err(|e| e.to_string())?;
    let mut zip = zip::ZipWriter::new(file);
    let options = zip::write::SimpleFileOptions::default()
        .compression_method(zip::CompressionMethod::Deflated);

    let walkdir = walkdir::WalkDir::new(src_dir);
    let it = walkdir.into_iter().filter_map(|e| e.ok());

    for entry in it {
        let path = entry.path();
        let name = path.strip_prefix(src_dir).map_err(|e| e.to_string())?;

        if path.is_file() {
            debug!("Adding file to zip: {:?}", name);
            zip.start_file(name.to_string_lossy().to_string(), options)
                .map_err(|e| e.to_string())?;
            let mut f = fs::File::open(path).map_err(|e| e.to_string())?;
            std::io::copy(&mut f, &mut zip).map_err(|e| e.to_string())?;
        } else if !name.as_os_str().is_empty() {
            debug!("Adding directory to zip: {:?}", name);
            zip.add_directory(name.to_string_lossy().to_string(), options)
                .map_err(|e| e.to_string())?;
        }
    }

    zip.finish().map_err(|e| e.to_string())?;
    Ok(())
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
            "input-method" => {
                input_method = field.text().await.map_err(|e| e.to_string())?;
                debug!("Got input method: {}", input_method);
            }
            "code" => {
                let code_text = field.text().await.map_err(|e| e.to_string())?;
                debug!("Got code field content length: {}", code_text.len());
                if input_method == "code" {
                    code = code_text;
                    debug!("Using code from textarea");
                } else {
                    debug!("Ignoring code field because input method is: {}", input_method);
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
    info!("Using absolute file path: {:?}", abs_file_path);
    info!("Using absolute data dir: {:?}", abs_data_dir);

    // Run PCG analysis using pcg-bin
    let result = run_pcg_analysis(abs_file_path, abs_data_dir);

    if let Err(e) = result {
        let error_message = format!("PCG analysis failed: {}", e);
        return Ok((StatusCode::INTERNAL_SERVER_ERROR, error_message).into_response());
    }

    // Zip the data directory
    let data_zip_path = unique_dir.join("data.zip");
    zip_directory(&data_dir, &data_zip_path)?;
    info!("Created data.zip at {:?}", data_zip_path);

    // Redirect to local visualization with data source URL
    let unique_dir_name = unique_dir.file_name().unwrap().to_str().unwrap();
    let redirect_url = format!(
        "/visualization/?datasrc=/tmp/{}",
        unique_dir_name
    );
    Ok(Redirect::to(&redirect_url).into_response())
}

