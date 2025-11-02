#!/bin/sh
export LD_LIBRARY_PATH=$(rustc --print sysroot)/lib:$LD_LIBRARY_PATH
exec target/release/pcg-server "$@"

