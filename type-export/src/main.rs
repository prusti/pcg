#![feature(rustc_private)]

use specta_typescript::{BigIntExportBehavior, Typescript};
use std::fs;
use std::path::PathBuf;

fn main() {
    let output_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("Failed to get parent directory")
        .join("visualization")
        .join("src")
        .join("generated");

    fs::create_dir_all(&output_dir).expect("Failed to create output directory");

    let output_file = output_dir.join("types.ts");

    let typescript = Typescript::default()
        .bigint(BigIntExportBehavior::Number);

    let header = "import type { StringOf } from \"../generated_type_deps.ts\";\n";

    let collection = pcg::type_collection();
    let contents = typescript.export(&collection).unwrap();

    fs::write(&output_file, format!("{}{}", header, contents)).unwrap();

    println!("TypeScript types generated at: {}", output_file.display());
}
