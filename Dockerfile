# Build stage for Node.js visualization
FROM node:20 AS node-builder

WORKDIR /usr/src/app/visualization

# Copy visualization project files
COPY visualization/package*.json ./
RUN npm install

COPY visualization/ ./
RUN npm run build

# Backend stage - build and run with Rust
FROM rust:1.91

# Install required dependencies
RUN apt-get update && apt-get install -y \
    pkg-config \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /usr/src/app

# Copy rust-toolchain to ensure correct Rust version
COPY rust-toolchain ./

# Ensure the toolchain is installed
RUN rustup show

# Copy all project files
COPY . .

# Copy built visualization from node-builder
RUN mkdir -p /usr/src/app/visualization/dist
COPY --from=node-builder /usr/src/app/visualization/dist /usr/src/app/visualization/dist/
COPY --from=node-builder /usr/src/app/visualization/index.html /usr/src/app/visualization/index.html

# Create tmp directory with proper permissions
RUN mkdir -p pcg-server/tmp && chmod 777 pcg-server/tmp

# Enable full backtraces
ENV RUST_BACKTRACE=1

# Expose port for pcg-server
EXPOSE 4000

# Run pcg-server
WORKDIR /usr/src/app/pcg-server

RUN cargo build --release
CMD ["cargo", "run", "--release"]
