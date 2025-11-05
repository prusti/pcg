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
