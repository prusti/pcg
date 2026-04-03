#!/usr/bin/env bash
# Collects LLVM source-based code coverage for the pcg crate.
#
# Coverage is gathered from:
#   1. Unit tests (cargo test -p pcg --lib)
#   2. All pcg-tests (test-files, aliases, visualization, etc.)
#
# The pcg-tests invoke the pcg-bin debug binary on test-files and
# test-crates, so coverage of code paths exercised by integration
# tests is also captured.
#
# Requirements:
#   - Nightly Rust toolchain with llvm-tools-preview component
#
# Usage:
#   ./scripts/coverage.sh [--html | --lcov | --text]
#
# Output:
#   coverage/           - profraw files and merged profile
#   coverage/lcov.info  - LCOV report (with --lcov, default)
#   coverage/html/      - HTML report (with --html)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
COVERAGE_DIR="$PROJECT_DIR/coverage"
PROFRAW_DIR="$COVERAGE_DIR/profraw"

OUTPUT_FORMAT="${1:---lcov}"

rm -rf "$COVERAGE_DIR"
mkdir -p "$PROFRAW_DIR"

RUSTUP_SYSROOT="$(rustc --print sysroot)"
LLVM_PROFDATA="$(find "$RUSTUP_SYSROOT" -name llvm-profdata -type f | head -1)"
LLVM_COV="$(find "$RUSTUP_SYSROOT" -name llvm-cov -type f | head -1)"

if [ -z "$LLVM_PROFDATA" ] || [ -z "$LLVM_COV" ]; then
    echo "Error: llvm-tools not found."
    echo "Install with: rustup component add llvm-tools-preview"
    exit 1
fi

echo "Using llvm-profdata: $LLVM_PROFDATA"
echo "Using llvm-cov: $LLVM_COV"

export RUSTFLAGS="-C instrument-coverage"
export LLVM_PROFILE_FILE="$PROFRAW_DIR/coverage-%p-%m.profraw"

# Step 1: Run unit tests with coverage
echo "=== Running unit tests with coverage ==="
cargo test -p pcg --lib --manifest-path "$PROJECT_DIR/Cargo.toml"

# Step 2: Run all pcg-tests with coverage
# This builds pcg-bin internally and invokes it on test-files,
# so the instrumented pcg-bin writes profraw data too.
echo "=== Running pcg-tests with coverage ==="
(cd "$PROJECT_DIR/pcg-tests" && cargo test -- --nocapture)

# Step 3: Merge profraw files
echo "=== Merging profile data ==="
PROFRAW_COUNT="$(find "$PROFRAW_DIR" -name '*.profraw' | wc -l)"
if [ "$PROFRAW_COUNT" -eq 0 ]; then
    echo "Error: No profraw files generated."
    exit 1
fi
echo "Merging $PROFRAW_COUNT profile files"
"$LLVM_PROFDATA" merge -sparse "$PROFRAW_DIR"/*.profraw \
    -o "$COVERAGE_DIR/coverage.profdata"

# Collect all instrumented binaries for the report.
PCG_BIN="$PROJECT_DIR/pcg-bin/target/debug/pcg_bin"
OBJECT_ARGS=()
if [ -f "$PCG_BIN" ]; then
    OBJECT_ARGS+=("--object" "$PCG_BIN")
fi
while IFS= read -r bin; do
    OBJECT_ARGS+=("--object" "$bin")
done < <(find "$PROJECT_DIR/target/debug/deps" \
    -name 'pcg-*' -type f -executable 2>/dev/null)

if [ ${#OBJECT_ARGS[@]} -eq 0 ]; then
    echo "Error: No instrumented binaries found."
    exit 1
fi

# Only report on pcg library source files
IGNORE_REGEX='(/.cargo/|/rustc/|pcg-tests/|pcg-bin/|pcg-server/'
IGNORE_REGEX+='|pcg-macros/|borrowck-body-storage/|type-export/)'

# Step 4: Generate report
echo "=== Generating coverage report ==="
case "$OUTPUT_FORMAT" in
    --html)
        "$LLVM_COV" show \
            "${OBJECT_ARGS[@]}" \
            --instr-profile="$COVERAGE_DIR/coverage.profdata" \
            --format=html \
            --output-dir="$COVERAGE_DIR/html" \
            --ignore-filename-regex="$IGNORE_REGEX" \
            --show-line-counts-or-regions \
            --Xdemangler=rustfilt 2>/dev/null || \
        "$LLVM_COV" show \
            "${OBJECT_ARGS[@]}" \
            --instr-profile="$COVERAGE_DIR/coverage.profdata" \
            --format=html \
            --output-dir="$COVERAGE_DIR/html" \
            --ignore-filename-regex="$IGNORE_REGEX" \
            --show-line-counts-or-regions
        echo "HTML report: $COVERAGE_DIR/html/index.html"
        ;;
    --lcov)
        "$LLVM_COV" export \
            "${OBJECT_ARGS[@]}" \
            --instr-profile="$COVERAGE_DIR/coverage.profdata" \
            --format=lcov \
            --ignore-filename-regex="$IGNORE_REGEX" \
            > "$COVERAGE_DIR/lcov.info"
        echo "LCOV report: $COVERAGE_DIR/lcov.info"
        ;;
    --text)
        "$LLVM_COV" report \
            "${OBJECT_ARGS[@]}" \
            --instr-profile="$COVERAGE_DIR/coverage.profdata" \
            --ignore-filename-regex="$IGNORE_REGEX"
        ;;
    *)
        echo "Unknown format: $OUTPUT_FORMAT"
        echo "Usage: $0 [--html | --lcov | --text]"
        exit 1
        ;;
esac

# Print summary
echo ""
echo "=== Coverage Summary ==="
"$LLVM_COV" report \
    "${OBJECT_ARGS[@]}" \
    --instr-profile="$COVERAGE_DIR/coverage.profdata" \
    --ignore-filename-regex="$IGNORE_REGEX" 2>/dev/null | tail -1 || true

echo ""
echo "Profile data: $COVERAGE_DIR/coverage.profdata"
echo "Raw profiles: $PROFRAW_DIR/"
