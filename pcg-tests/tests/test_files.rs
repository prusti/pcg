#[allow(unused)]
use rayon::prelude::*;
use std::path::PathBuf;

mod common;

#[test]
fn check_test_files() {
    // Build the debug binary first
    common::build_pcg_bin(common::Target::Debug);

    // Get the workspace directory from CARGO_MANIFEST_DIR
    let workspace_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());

    // Find all numbered test files
    let test_dir = workspace_dir.parent().unwrap().join("test-files");

    let mut test_files = common::get_test_files(&test_dir);

    test_files.sort_by(|a, b| {
        let a_lines = std::fs::read_to_string(a).unwrap().lines().count();
        let b_lines = std::fs::read_to_string(b).unwrap().lines().count();
        a_lines.cmp(&b_lines)
    });

    // test_files.par_iter().panic_fuse().for_each(|test_file| {
    //     common::run_pcg_on_file(test_file);
    // });

    test_files.iter().for_each(|test_file| {
        common::run_pcg_on_file(test_file);
    });
}

/// `PCG_ALLOW_BORROWCK_ERRORS` discards borrow check errors only: the files in
/// `test-files/errors` whose names start with `allowed_` must succeed, and the
/// others, which also have an error that borrow checking does not report,
/// must fail.
#[test]
fn only_borrowck_errors_are_allowed() {
    common::build_pcg_bin(common::Target::Debug);
    let workspace_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    let error_dir = workspace_dir
        .parent()
        .unwrap()
        .join("test-files")
        .join("errors");
    let mut files = std::fs::read_dir(&error_dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect::<Vec<_>>();
    files.sort();
    assert!(!files.is_empty());
    for file in files {
        let allowed = file
            .file_name()
            .unwrap()
            .to_str()
            .unwrap()
            .starts_with("allowed_");
        assert_eq!(
            common::pcg_on_file_succeeds(&file),
            allowed,
            "{} should {}",
            file.display(),
            if allowed { "succeed" } else { "fail" }
        );
    }
}
