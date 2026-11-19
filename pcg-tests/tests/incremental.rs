mod common;

use common::{RunOnCrateOptions, Target, run_pcg_on_crate_in_dir};

/// Cargo compiles the primary package incrementally (forced here, since the environment
/// may turn it off). After an edit, rustc reuses the borrowck results of the unchanged
/// bodies, so the PCG must still get their bodies.
#[test]
fn rerun_after_edit() {
    let dir = std::env::temp_dir().join(format!("pcg-incremental-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(
        dir.join("Cargo.toml"),
        "[package]\nname = \"incremental\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[workspace]\n",
    )
    .unwrap();
    let unchanged = "pub fn unchanged(x: &mut i32) -> &mut i32 { *x += 1; x }\n";
    let options = RunOnCrateOptions::RunPCG {
        target: Target::Debug,
        validity_checks: true,
        function: None,
        extra_env_vars: vec![("CARGO_INCREMENTAL".to_string(), "1".to_string())],
    };
    std::fs::write(dir.join("src/lib.rs"), unchanged).unwrap();
    assert!(run_pcg_on_crate_in_dir(&dir, options.clone()));
    std::fs::write(
        dir.join("src/lib.rs"),
        format!("{unchanged}pub fn added(x: &mut i32) -> i32 {{ *x }}\n"),
    )
    .unwrap();
    assert!(run_pcg_on_crate_in_dir(&dir, options));
    std::fs::remove_dir_all(&dir).unwrap();
}
