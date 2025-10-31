# Type Export Tool

This tool generates TypeScript types from Rust types using `specta`.

## Why a Separate Crate?

This tool is in a separate crate to keep type generation separate from the main compilation flow. By using `#![feature(rustc_private)]`, it can directly import types from the `pcg` crate without duplication.

## Usage

To regenerate the TypeScript types after modifying Rust types:

```bash
cd type-export
cargo run --release
```

The generated types will be written to `pcg-bin/visualization/src/generated/types.ts`.

## Adding New Types

1. **Define the type in the main crate** (`src/visualization/mir_graph.rs` or similar):
   ```rust
   #[derive(Deserialize, Serialize, Debug, Clone, PartialEq, Eq, Hash)]
   #[cfg_attr(feature = "type-export", derive(specta::Type))]
   #[cfg_attr(feature = "type-export", specta(export = false))]
   pub struct MyType {
       #[cfg_attr(feature = "type-export", specta(type = u32))]
       pub field: usize,
   }
   ```

2. **Export it from the visualization module** if needed:
   ```rust
   #[cfg(feature = "type-export")]
   pub use mir_graph::MyType;
   ```

3. **Update `type-export/src/main.rs`** to import and export your new type:
   ```rust
   use pcg::visualization::MyType;
   ```

4. **Update the export call** to include your new type:
   ```rust
   let exports = format!("{}\n\nexport type {{ MyType }}\n\n{}",
       specta_typescript::export::<SourcePos>(&Default::default())?,
       specta_typescript::export::<MyType>(&Default::default())?
   );
   ```

4. **Run the tool** to generate the TypeScript types.

5. **Import and use** the generated types in your TypeScript code:
   ```typescript
   import type { MyType } from "./generated/types";
   ```

## Important Notes

- Use `#[specta(type = u32)]` for `usize` fields to avoid BigInt issues in TypeScript
- The `#[specta(export = false)]` attribute prevents automatic export (we control it manually)
- Types are imported directly from the `pcg` crate, so there's a single source of truth

