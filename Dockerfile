# Build stage for Node.js assets
FROM node:20 AS node-builder

# Build visualization assets
WORKDIR /usr/src/app/visualization
COPY visualization/package*.json ./
RUN npm install
COPY visualization/ ./
RUN npm run build

# Build pcg-server JavaScript assets
WORKDIR /usr/src/app/pcg-server
COPY pcg-server/package*.json ./
RUN npm install
COPY pcg-server/tsconfig.json pcg-server/webpack.config.js ./
COPY pcg-server/src ./src
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

# Add the target for the platform we're running on (after files are copied)
RUN rustup target add $(rustc -vV | grep 'host:' | awk '{print $2}')

# Copy built assets from node-builder
RUN mkdir -p /usr/src/app/visualization/dist /usr/src/app/pcg-server/static
COPY --from=node-builder /usr/src/app/visualization/dist /usr/src/app/visualization/dist/
COPY --from=node-builder /usr/src/app/visualization/index.html /usr/src/app/visualization/index.html
COPY --from=node-builder /usr/src/app/pcg-server/static /usr/src/app/pcg-server/static/

# Create tmp directory with proper permissions
RUN mkdir -p pcg-server/tmp && chmod 777 pcg-server/tmp

# Enable full backtraces
ENV RUST_BACKTRACE=1

# Expose port for pcg-server
EXPOSE 4000

# Build pcg-bin first (required by pcg-server)
# Note: pcg-bin has its own workspace, so we need to build it in its directory
WORKDIR /usr/src/app/pcg-bin
RUN cargo build --release

# Build pcg-server
WORKDIR /usr/src/app/pcg-server
RUN cargo build --release

# Set LD_LIBRARY_PATH to include rustc libraries from the sysroot
RUN RUSTC_SYSROOT=$(rustc --print sysroot) && \
    echo "$RUSTC_SYSROOT/lib" > /etc/ld.so.conf.d/rustc.conf && \
    ldconfig

# Copy and set up the start script
COPY pcg-server/start-server.sh /usr/local/bin/start-server.sh
RUN chmod +x /usr/local/bin/start-server.sh

CMD ["/usr/local/bin/start-server.sh"]
