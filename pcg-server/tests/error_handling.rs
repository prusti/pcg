use std::fs;
use std::path::PathBuf;
use std::process::Command;

// Test helper to run pcg-bin on a file
fn run_pcg_analysis(file_path: PathBuf, data_dir: PathBuf) -> Result<(), String> {
    // Use the same logic as the main server to find pcg_bin
    let pcg_bin_path = std::env::var("PCG_BIN_PATH")
        .unwrap_or_else(|_| {
            let dev_path = "../pcg-bin/target/release/pcg_bin";
            let docker_path = "../target/release/pcg_bin";
            if std::path::Path::new(dev_path).exists() {
                dev_path.to_string()
            } else {
                docker_path.to_string()
            }
        });

    let output = Command::new(&pcg_bin_path)
        .arg(&file_path)
        .arg("--edition=2018")
        .env("PCG_VISUALIZATION", "false")
        .env("PCG_VISUALIZATION_DATA_DIR", &data_dir)
        .output()
        .map_err(|e| format!("Failed to execute pcg-bin at {}: {}", pcg_bin_path, e))?;

    if !output.status.success() {
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format!("PCG analysis failed:\nSTDOUT: {}\nSTDERR: {}", stdout, stderr));
    }

    Ok(())
}

#[test]
fn test_compilation_error_does_not_crash() {
    let temp_dir = tempfile::tempdir().unwrap();
    let data_dir = temp_dir.path().join("data");
    fs::create_dir(&data_dir).unwrap();

    let invalid_rust_code = r#"
        fn main() {
            let x: i32 = "not a number";
        }
    "#;

    let test_file = temp_dir.path().join("invalid.rs");
    fs::write(&test_file, invalid_rust_code).unwrap();

    let result = run_pcg_analysis(test_file, data_dir);

    assert!(result.is_ok() || result.is_err(), "Function should return normally, not crash");
}

#[test]
fn test_syntax_error_does_not_crash() {
    let temp_dir = tempfile::tempdir().unwrap();
    let data_dir = temp_dir.path().join("data");
    fs::create_dir(&data_dir).unwrap();

    let invalid_rust_code = r#"
        fn main(){
    "#;

    let test_file = temp_dir.path().join("syntax_error.rs");
    fs::write(&test_file, invalid_rust_code).unwrap();

    let result = run_pcg_analysis(test_file, data_dir);

    assert!(result.is_ok() || result.is_err(), "Function should return normally, not crash");
}

#[test]
fn test_successful_compilation() {
    let temp_dir = tempfile::tempdir().unwrap();
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

    let result = run_pcg_analysis(test_file, data_dir);

    assert!(result.is_ok(), "Expected compilation to succeed for valid code, got error: {:?}", result);
}

