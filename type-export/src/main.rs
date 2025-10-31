#![feature(rustc_private)]

use pcg::visualization::SourcePos;
use specta_typescript::Typescript;
use specta::Type;
use std::fs;
use std::path::PathBuf;

fn main() {
    let output_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("Failed to get parent directory")
        .join("pcg-bin")
        .join("visualization")
        .join("src")
        .join("generated");

    fs::create_dir_all(&output_dir).expect("Failed to create output directory");

    let output_file = output_dir.join("types.ts");

    specta::export::ts(output_file.to_str().unwrap()).unwrap();

    println!("TypeScript types generated at: {}", output_file.display());
}

