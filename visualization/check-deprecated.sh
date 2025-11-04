#!/bin/bash
set -e

echo "Checking for deprecated npm packages..."

# Check direct dependencies for deprecation
OUTPUT=$(npx check-is-deprecated -f package.json -a 2>&1)

# Look for any deprecated packages (marked with ✖)
if echo "$OUTPUT" | grep -q "✖"; then
    echo "ERROR: Deprecated packages found:"
    echo "$OUTPUT" | grep -B1 "✖"
    exit 1
fi

# Check for deprecation warnings during install
INSTALL_OUTPUT=$(npm install --no-save 2>&1 || true)
if echo "$INSTALL_OUTPUT" | grep -qi "deprecated"; then
    echo "ERROR: Deprecation warnings found during npm install:"
    echo "$INSTALL_OUTPUT" | grep -i "deprecated"
    exit 1
fi

echo "✓ No deprecated packages found"
exit 0

