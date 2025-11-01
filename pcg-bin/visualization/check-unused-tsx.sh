#!/bin/bash

# Script to check for unused .tsx files in the visualization project
# Exit with code 1 if unused .tsx files are found, 0 otherwise

set -e

cd "$(dirname "$0")"

echo "Checking for unused .tsx files..."

# Find all .tsx files
tsx_files=$(find src -name "*.tsx" | sort)

# Entry point is src/script.tsx
entry_point="src/script.tsx"

unused_count=0
unused_files=""

for file in $tsx_files; do
  # Get the file path relative to src/
  relative_path=${file#src/}

  # Get the filename without extension
  basename_no_ext=$(basename "$file" .tsx)

  # Check if this is the entry point
  if [ "$file" = "$entry_point" ]; then
    continue
  fi

  # Check if the file is imported anywhere
  # Look for imports like: from "./ComponentName" or from "../components/ComponentName"
  # TypeScript allows importing without extensions
  found=false

  # Search for any import statement that references this file's basename
  if grep -rq "from ['\"].*/${basename_no_ext}['\"]" src --include="*.tsx" --include="*.ts"; then
    found=true
  # Also check for imports without the leading path (e.g., from "./ComponentName")
  elif grep -rq "from ['\"]\./${basename_no_ext}['\"]" src --include="*.tsx" --include="*.ts"; then
    found=true
  # Check for imports with .tsx extension
  elif grep -rq "from ['\"].*/${basename_no_ext}\.tsx['\"]" src --include="*.tsx" --include="*.ts"; then
    found=true
  fi

  if [ "$found" = false ]; then
    echo "❌ Unused: $file"
    unused_files="$unused_files\n  - $file"
    unused_count=$((unused_count + 1))
  fi
done

if [ $unused_count -gt 0 ]; then
  echo ""
  echo "Found $unused_count unused .tsx file(s):"
  echo -e "$unused_files"
  echo ""
  echo "Please remove these files or add them to the import tree."
  exit 1
else
  echo "✅ No unused .tsx files found."
  exit 0
fi

