#![feature(rustc_private)]

use specta_typescript::{BigIntExportBehavior, Typescript};
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

    let typescript = Typescript::default().bigint(BigIntExportBehavior::Number);

    let collection = pcg::type_collection();
    typescript
        .export_to(&output_file, &collection)
        .unwrap();

    println!("TypeScript types generated at: {}", output_file.display());
}
