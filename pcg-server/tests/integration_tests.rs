//! Integration tests for pcg-server
//!
//! These tests require a running server instance and are ignored by default.
//!
//! To run these tests:
//! 1. Start the server on port 4001: `cd pcg-server && cargo run` (or modify get_server_url())
//! 2. Run: `cargo test --test integration_tests -- --ignored --test-threads=1`
//!
//! The tests verify that the server correctly handles:
//! - File uploads with valid Rust code
//! - Code textarea input with valid Rust code
//! - Empty code returning BAD_REQUEST error
//! - Non-Rust files being rejected
//! - Compilation errors being returned to the user

#![feature(rustc_private)]
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

use reqwest::blocking::{multipart, Client};
use std::fs;
use std::thread;
use std::time::Duration;
use tempfile::TempDir;

fn get_server_url() -> String {
    "http://localhost:4001".to_string()
}

fn wait_for_server(url: &str, max_attempts: u32) -> bool {
    for _ in 0..max_attempts {
        if Client::new().get(url).send().is_ok() {
            return true;
        }
        thread::sleep(Duration::from_millis(100));
    }
    false
}

#[test]
#[ignore] // Run with: cargo test --test integration_tests -- --ignored --test-threads=1
fn test_file_upload_integration() {
    let server_url = get_server_url();

    if !wait_for_server(&server_url, 10) {
        println!("Skipping integration test - server not running on {}", server_url);
        return;
    }

    let temp_dir = TempDir::new().unwrap();
    let test_file = temp_dir.path().join("test.rs");
    let valid_rust_code = r#"
fn main() {
    let x: i32 = 42;
    println!("{}", x);
}
"#;
    fs::write(&test_file, valid_rust_code).unwrap();

    let form = multipart::Form::new()
        .text("input-method", "file")
        .file("file", test_file.to_str().unwrap())
        .unwrap();

    let client = Client::new();
    let response = client
        .post(&format!("{}/upload", server_url))
        .multipart(form)
        .send();

    match response {
        Ok(resp) => {
            assert!(
                resp.status().is_success() || resp.status().is_redirection(),
                "Expected success or redirect, got: {:?}",
                resp.status()
            );
        }
        Err(e) => {
            panic!("Request failed: {}", e);
        }
    }
}

#[test]
#[ignore] // Run with: cargo test --test integration_tests -- --ignored --test-threads=1
fn test_code_textarea_integration() {
    let server_url = get_server_url();

    if !wait_for_server(&server_url, 10) {
        println!("Skipping integration test - server not running on {}", server_url);
        return;
    }

    let valid_rust_code = r#"
fn main() {
    let x: i32 = 42;
    println!("{}", x);
}
"#;

    let form = multipart::Form::new()
        .text("input-method", "code")
        .text("code", valid_rust_code);

    let client = Client::new();
    let response = client
        .post(&format!("{}/upload", server_url))
        .multipart(form)
        .send();

    match response {
        Ok(resp) => {
            assert!(
                resp.status().is_success() || resp.status().is_redirection(),
                "Expected success or redirect, got: {:?}",
                resp.status()
            );
        }
        Err(e) => {
            panic!("Request failed: {}", e);
        }
    }
}

#[test]
#[ignore] // Run with: cargo test --test integration_tests -- --ignored --test-threads=1
fn test_empty_code_returns_bad_request() {
    let server_url = get_server_url();

    if !wait_for_server(&server_url, 10) {
        println!("Skipping integration test - server not running on {}", server_url);
        return;
    }

    let form = multipart::Form::new()
        .text("input-method", "code")
        .text("code", "");

    let client = Client::new();
    let response = client
        .post(&format!("{}/upload", server_url))
        .multipart(form)
        .send();

    match response {
        Ok(resp) => {
            assert_eq!(
                resp.status(),
                reqwest::StatusCode::BAD_REQUEST,
                "Expected BAD_REQUEST for empty code"
            );
            let body = resp.text().unwrap();
            assert!(
                body.contains("No code content provided"),
                "Expected error message about no code content"
            );
        }
        Err(e) => {
            panic!("Request failed: {}", e);
        }
    }
}

#[test]
#[ignore] // Run with: cargo test --test integration_tests -- --ignored --test-threads=1
fn test_non_rust_file_rejected() {
    let server_url = get_server_url();

    if !wait_for_server(&server_url, 10) {
        println!("Skipping integration test - server not running on {}", server_url);
        return;
    }

    let temp_dir = TempDir::new().unwrap();
    let test_file = temp_dir.path().join("test.txt");
    fs::write(&test_file, "not rust code").unwrap();

    let form = multipart::Form::new()
        .text("input-method", "file")
        .file("file", test_file.to_str().unwrap())
        .unwrap();

    let client = Client::new();
    let response = client
        .post(&format!("{}/upload", server_url))
        .multipart(form)
        .send();

    match response {
        Ok(resp) => {
            assert_eq!(
                resp.status(),
                reqwest::StatusCode::BAD_REQUEST,
                "Expected BAD_REQUEST for non-Rust file"
            );
        }
        Err(e) => {
            panic!("Request failed: {}", e);
        }
    }
}

#[test]
#[ignore] // Run with: cargo test --test integration_tests -- --ignored --test-threads=1
fn test_compilation_error_returns_error() {
    let server_url = get_server_url();

    if !wait_for_server(&server_url, 10) {
        println!("Skipping integration test - server not running on {}", server_url);
        return;
    }

    let invalid_rust_code = r#"
fn main() {
    let x: i32 = "not a number";
}
"#;

    let form = multipart::Form::new()
        .text("input-method", "code")
        .text("code", invalid_rust_code);

    let client = Client::new();
    let response = client
        .post(&format!("{}/upload", server_url))
        .multipart(form)
        .send();

    match response {
        Ok(resp) => {
            assert_eq!(
                resp.status(),
                reqwest::StatusCode::INTERNAL_SERVER_ERROR,
                "Expected INTERNAL_SERVER_ERROR for compilation error"
            );
            let body = resp.text().unwrap();
            assert!(
                body.contains("Compilation failed"),
                "Expected compilation error message"
            );
        }
        Err(e) => {
            panic!("Request failed: {}", e);
        }
    }
}

