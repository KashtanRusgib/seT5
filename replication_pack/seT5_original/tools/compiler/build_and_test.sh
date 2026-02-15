#!/bin/bash
# Build and test script for Ternary C Compiler
# Exit code: 0 = all pass, 1 = failure
set -e

echo "=== Building Ternary C Compiler ==="
cd "$(dirname "$0")"

make clean
make

echo ""
echo "=== Test: ./ternary_compiler dummy ==="
echo "(Should output 'Result: 7')"
./ternary_compiler dummy

echo ""
echo "=== Test: Standalone VM test ==="
echo "(Should output 'Result: 7')"
./vm_test

echo ""
echo "=== Running Full Test Suite ==="
make test

echo ""
echo "=== All builds and tests complete! ==="
