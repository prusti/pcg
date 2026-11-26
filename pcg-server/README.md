# PCG Viewer Server

A web server for visualizing PCG outputs. This server allows users to upload Rust files and view their PCG visualizations through a web interface.

## Prerequisites

- NPM, Rust and Cargo installed

## Setup

Run the following commands to build the project:

```bash
npm install
cargo build
```

## Running the Server

1. Start the server:

```bash
cargo run
```

2. Open your web browser and navigate to `http://localhost:4000`
3. Upload a Rust file through the web interface
4. After successful processing, you'll be automatically redirected to view the PCG visualization

The visualization remains available at its unique URL until the server is restarted

The upload form defaults to **Rust SVG**. Select **Graphviz (legacy)** to run the
analysis with `PCG_LEGACY_GRAPH_RENDERER=true` and generate DOT graphs only.
Setting that environment variable when starting the server changes the form's
default; an explicit form selection overrides it.

In the viewer, **Settings → PCG renderer** switches between the generated formats.
Default snapshots include both formats. Legacy snapshots and older archives
contain only DOT; the viewer identifies that fallback when Rust SVG is selected.
