# PCG Binary

This is a standalone binary that demonstrates how to use the PCG library as a Rust compiler plugin.

## Overview

`pcg-bin` is a Rust compiler wrapper that runs the PCG (Place Capability Graphs) analysis on all functions within a Rust source file. It can optionally produce visualizations of the analysis outputs.

## Usage

Run the binary on a Rust source file:

```bash
cargo run -p pcg_bin [FILENAME].rs
```

### With Visualization

To generate visualization output:

```bash
PCG_VISUALIZATION=true cargo run -p pcg_bin [FILENAME].rs
```

## Implementation

The main implementation is in [`src/main.rs`](./src/main.rs), which shows how to:

1. Set up the PCG library as a dependency
2. Implement a Rust compiler callback using the `PcgCallbacks` from the PCG library
3. Configure the compiler to run the PCG analysis
4. Optionally enable memory profiling features

This serves as a reference example for integrating the PCG library into other projects.

