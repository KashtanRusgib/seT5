#!/bin/bash

# Exit on any error
set -e

# Ensure we're in the compiler repo
if [ ! -f "README.md" ] || ! grep -q "Ternary C Compiler" README.md; then
  echo "Error: This script must be run from the Ternary-C-compiler repo root."
  exit 1
fi

# Push the compiler repo to origin (main branch)
echo "Pushing Ternary-C-compiler to origin..."
git push -u origin main

# Tag a stable version for submodule pinning
git tag v1.0 || true  # Skip if tag exists
git push --tags

# Clone seT5 into a temp dir in the workspace
echo "Cloning seT5 into /workspaces/set5-temp..."
cd /workspaces
git clone https://github.com/KashtanRusgib/seT5 set5-temp
cd set5-temp

# Add the compiler as a submodule in tools/compiler
echo "Adding Ternary-C-compiler as submodule..."
mkdir -p tools
git submodule add https://github.com/KashtanRusgib/Ternary-C-compiler tools/compiler

# Pin to v1.0 for stability
cd tools/compiler
git checkout v1.0
cd ../..

# Commit and push the change to seT5
git add .gitmodules tools/compiler
git commit -m "Add Ternary-C-compiler as submodule (v1.0) for builds"
echo "Pushing updates to seT5 origin..."
git push origin main

echo "Done! seT5 is updated with the submodule. You can now cd to /workspaces/set5-temp to continue development."
echo "To init submodules in future clones: git submodule update --init --recursive"
