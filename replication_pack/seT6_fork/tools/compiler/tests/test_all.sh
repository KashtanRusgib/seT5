#!/bin/bash
# test_all.sh - Run all test suites and report results
# Returns non-zero if ANY test suite fails.
set -o pipefail

PASS=0
FAIL=0
FAILED_SUITES=""

cd "$(dirname "$0")/.."

run_suite() {
    local name="$1"
    local binary="$2"
    
    echo ""
    echo "--- Running: $name ---"
    if ./"$binary" 2>&1; then
        PASS=$((PASS + 1))
    else
        FAIL=$((FAIL + 1))
        FAILED_SUITES="$FAILED_SUITES $name"
    fi
}

echo "========================================"
echo "  Ternary Compiler - Full Test Suite"
echo "========================================"

run_suite "Trit Operations" "test_trit"
run_suite "Lexer/Tokenizer" "test_lexer"
run_suite "Code Generator"  "test_codegen"
run_suite "VM Execution"    "test_vm"
run_suite "Logger"          "test_logger"
run_suite "Integration"     "test_integration"

echo ""
echo "========================================"
echo "  Summary: $PASS passed, $FAIL failed"
if [ $FAIL -gt 0 ]; then
    echo "  FAILED:$FAILED_SUITES"
    echo "========================================"
    exit 1
else
    echo "  ALL TESTS PASSED"
    echo "========================================"
    exit 0
fi
