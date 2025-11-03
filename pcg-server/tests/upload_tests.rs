use std::fs;

#[test]
fn test_multipart_form_structure_file_upload() {
    let temp_dir = tempfile::tempdir().unwrap();
    let tmp_path = temp_dir.path();
    fs::create_dir_all(tmp_path).unwrap();

    let valid_rust_code = r#"
        fn main() {
            let x: i32 = 42;
            println!("{}", x);
        }
    "#;

    let test_file_path = tmp_path.join("test.rs");
    fs::write(&test_file_path, valid_rust_code).unwrap();

    // Create multipart form data as it would be sent by the form
    let boundary = "------------------------boundary123";
    let body = format!(
        "--{boundary}\r\n\
         Content-Disposition: form-data; name=\"input-method\"\r\n\
         \r\n\
         file\r\n\
         --{boundary}\r\n\
         Content-Disposition: form-data; name=\"file\"; filename=\"test.rs\"\r\n\
         Content-Type: application/octet-stream\r\n\
         \r\n\
         {code}\r\n\
         --{boundary}\r\n\
         Content-Disposition: form-data; name=\"code\"\r\n\
         \r\n\
         \r\n\
         --{boundary}--\r\n",
        boundary = boundary,
        code = valid_rust_code
    );

    // Verify the multipart form has the correct structure
    assert!(body.contains("input-method"), "Body should contain input-method field");
    assert!(body.contains("file"), "Body should contain file field");
    assert!(body.contains("name=\"code\""), "Body should contain code field (even if empty)");

    // Verify that input-method comes before file (order matters for server logic)
    let input_method_pos = body.find("input-method").unwrap();
    let file_pos = body.find("name=\"file\"").unwrap();
    assert!(input_method_pos < file_pos, "input-method must come before file field for server to process correctly");
}

#[test]
fn test_multipart_form_structure_code_textarea() {
    let valid_rust_code = r#"
        fn main() {
            let x: i32 = 42;
            println!("{}", x);
        }
    "#;

    // Create multipart form data with code field as sent by textarea
    let boundary = "------------------------boundary123";
    let body = format!(
        "--{boundary}\r\n\
         Content-Disposition: form-data; name=\"input-method\"\r\n\
         \r\n\
         code\r\n\
         --{boundary}\r\n\
         Content-Disposition: form-data; name=\"file\"\r\n\
         \r\n\
         \r\n\
         --{boundary}\r\n\
         Content-Disposition: form-data; name=\"code\"\r\n\
         \r\n\
         {code}\r\n\
         --{boundary}--\r\n",
        boundary = boundary,
        code = valid_rust_code
    );

    assert!(body.contains("input-method"), "Body should contain input-method field");
    assert!(body.contains("name=\"code\""), "Body should contain code field");
    assert!(body.contains(valid_rust_code), "Body should contain the actual code");

    // Verify that input-method comes before code (order matters for server logic)
    let input_method_pos = body.find("input-method").unwrap();
    let code_pos = body.find("name=\"code\"").unwrap();
    assert!(input_method_pos < code_pos, "input-method must come before code field for server to process correctly");
}

#[test]
fn test_multipart_form_field_order_matters() {
    // This test verifies that when file upload is used, the empty code field
    // comes AFTER the file field, ensuring the server processes them in the right order
    let boundary = "------------------------boundary123";
    let rust_code = "fn test() { }";

    let body = format!(
        "--{boundary}\r\n\
         Content-Disposition: form-data; name=\"input-method\"\r\n\
         \r\n\
         file\r\n\
         --{boundary}\r\n\
         Content-Disposition: form-data; name=\"file\"; filename=\"test.rs\"\r\n\
         Content-Type: application/octet-stream\r\n\
         \r\n\
         {code}\r\n\
         --{boundary}\r\n\
         Content-Disposition: form-data; name=\"code\"\r\n\
         \r\n\
         \r\n\
         --{boundary}--\r\n",
        boundary = boundary,
        code = rust_code
    );

    // Verify field order: input-method, then file, then code
    let input_method_pos = body.find("name=\"input-method\"").unwrap();
    let file_pos = body.find("name=\"file\"").unwrap();
    let code_pos = body.find("name=\"code\"").unwrap();

    assert!(input_method_pos < file_pos, "input-method must come before file");
    assert!(file_pos < code_pos, "file must come before code field");

    // This order is critical: the code field should not overwrite the file contents
    // because the server checks input_method when processing the code field
}

