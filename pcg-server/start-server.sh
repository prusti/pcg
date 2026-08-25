#!/bin/sh
# This script is used to start the pcg-server in a Docker container
export LD_LIBRARY_PATH=$(rustc --print sysroot)/lib:$LD_LIBRARY_PATH
exec ${CARGO_TARGET_DIR:-target}/release/pcg-server "$@"

