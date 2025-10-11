# Place Capability Graphs (PCG) Analysis Library

This repository contains the Rust implementation of the PCG Analysis.

For more information about the PCG model, please checkout our [OOPSLA 2025 paper](https://arxiv.org/pdf/2503.21691).

## Usage as a Library

The PCG analysis can be easily included in Rust projects as a Cargo dependency.
The analysis is not available on crates.io (yet); the easiest way to include it
in your project is to include it as a `git` repository dependency in your
`Cargo.toml` as described
[here](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html#specifying-dependencies-from-git-repositories).

Note that our library interfaces with the Rust compiler APIs and therefore
requires that the project it is included in uses a nightly version of the Rust
compiler (this is typically specified via a `rust-toolchain` file in the parent
project). Although the compiler APIs in nightly Rust versions are unstable, our
implementation supports multiple versions by using conditional compilation based
on the compiler version. If you find that the library fails to compile for a
particular nightly release, please [file an
issue](https://github.com/prusti/pcg/issues/new).

### Example Project

This repository includes [`pcg-bin`](./pcg-bin), a standalone binary that
demonstrates how to use the PCG library. This binary can run the PCG analysis on
all functions within a Rust source file and optionally produce visualizations of
the analysis outputs. See the [`pcg-bin/src/main.rs`](./pcg-bin/src/main.rs)
file to see how the library is integrated into a Rust compiler plugin.

## Testing and Generating Debug Visualizations

The `pcg-bin` binary can be used to run the PCG analysis on all functions within
a Rust source file and (optionally) produce visualizations of the analysis
outputs that can be viewed via a web interface.

To run the binary on all functions in a Rust source file:

`cargo run [FILENAME].rs`

### Visualizing the PCG Analysis Output Results

To generate visualization output, set the `PCG_VISUALIZATION` environment
variable to `true` when running the tool, e.g.:

`PCG_VISUALIZATION=true cargo run [FILENAME.rs]`

To view the output, you need to run the visulization server, by running:

`cd visualization && ./serve`

Then, you can view the output graphs via the web interface at
`http://localhost:8080`.

Once the server is running, you can keep it running and analyze other files
(e.g. `PCG_VISUALIZATION=true cargo run [FILENAME2].rs`). Just
refresh the page to see updated results.
