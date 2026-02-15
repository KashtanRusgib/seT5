#!/usr/bin/env bash
# run_all_tests.sh — Master test runner for seT6 + Ternary-C-compiler
#
# Usage:  ./run_all_tests.sh
#
# Runs every test suite (compiler + seT6 kernel) in a single non-interactive
# command.  Results are printed to stdout AND saved to TEST_RESULTS/ with a
# timestamped filename:  yy-MM-dd-hh-mm-ss_all_tests.txt
#
# Exit code: 0 if all suites pass, 1 if any fail.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"

# ── timestamp & log setup ──────────────────────────────────────────────
TS="$(date '+%y-%m-%d-%H-%M-%S')"
RESULTS_DIR="$ROOT/TEST_RESULTS"
mkdir -p "$RESULTS_DIR"
LOGFILE="$RESULTS_DIR/${TS}_all_tests.txt"

TOTAL_SUITES=0
PASSED_SUITES=0
FAILED_SUITES=0
FAILED_LIST=""

# run_suite <label> <command…>
run_suite() {
    local label="$1"; shift
    TOTAL_SUITES=$((TOTAL_SUITES + 1))
    echo ""
    echo "========================================"
    echo "  $label"
    echo "========================================"
    if "$@"; then
        echo "  >> SUITE PASSED: $label"
        PASSED_SUITES=$((PASSED_SUITES + 1))
    else
        echo "  >> SUITE FAILED: $label"
        FAILED_SUITES=$((FAILED_SUITES + 1))
        FAILED_LIST="$FAILED_LIST  - $label\n"
    fi
}

# Everything below is captured to both the terminal and the log file.
{
    echo "seT6 Full Test Run — $TS"
    echo "========================================"
    echo ""

    # ── 1. Compiler tests ──────────────────────────────────────────────
    echo "########################################"
    echo "#  COMPILER TEST SUITES                #"
    echo "########################################"

    # Build compiler tests (non-interactive)
    make -C tools/compiler clean  >/dev/null 2>&1 || true
    make -C tools/compiler all    2>&1

    # Run each compiler test binary individually
    COMPILER_BINS=$(make -C tools/compiler -s -p 2>/dev/null | \
        grep '^TEST_BINS' | head -1 | sed 's/^TEST_BINS.*= *//')
    if [ -z "$COMPILER_BINS" ]; then
        # Fallback: enumerate known test binaries
        COMPILER_BINS="test_trit test_lexer test_parser test_codegen test_vm \
            test_logger test_ir test_sel4 test_integration test_memory test_set6 \
            test_bootstrap test_sel4_verify test_hardware test_basic \
            test_typechecker test_linker test_arrays test_selfhost \
            test_trit_edge_cases test_parser_fuzz test_performance \
            test_hardware_simulation test_ternary_edge_cases \
            test_ternary_arithmetic_comprehensive"
    fi

    for t in $COMPILER_BINS; do
        bin="tools/compiler/$t"
        if [ -x "$bin" ]; then
            run_suite "compiler/$t" "$bin"
        else
            echo "  [SKIP] $t (binary not found)"
        fi
    done

    # ── 2. seT6 kernel / integration tests ─────────────────────────────
    echo ""
    echo "########################################"
    echo "#  seT6 KERNEL TEST SUITES             #"
    echo "########################################"

    # Build all seT6 test binaries
    make set6_native           2>&1
    make test_integration      2>&1
    make test_sel4_ternary     2>&1
    make test_memory_safety    2>&1
    make test_scheduler_concurrency 2>&1
    make test_tbe              2>&1
    make test_trit_linux       2>&1

    run_suite "seT6/set6_native"                ./set6_native
    run_suite "seT6/test_integration"           ./test_integration
    run_suite "seT6/test_sel4_ternary"          ./test_sel4_ternary
    run_suite "seT6/test_memory_safety"         ./test_memory_safety
    run_suite "seT6/test_scheduler_concurrency" ./test_scheduler_concurrency
    run_suite "seT6/test_tbe"                   ./test_tbe
    run_suite "seT6/test_trit_linux"            ./test_trit_linux

    # ── 3. Trithon (Python) self-test ──────────────────────────────────
    echo ""
    echo "########################################"
    echo "#  TRITHON SELF-TEST                   #"
    echo "########################################"
    make build-trithon-ext 2>&1
    run_suite "trithon/self-test" python3 trithon/trithon.py

    # ── 4. TernBench ───────────────────────────────────────────────────
    echo ""
    echo "########################################"
    echo "#  TERNBENCH                           #"
    echo "########################################"
    run_suite "ternbench" python3 ternbench/ternbench.py

    # ── Summary ────────────────────────────────────────────────────────
    echo ""
    echo "========================================"
    echo "  MASTER TEST SUMMARY"
    echo "========================================"
    echo "  Total suites : $TOTAL_SUITES"
    echo "  Passed       : $PASSED_SUITES"
    echo "  Failed       : $FAILED_SUITES"
    if [ "$FAILED_SUITES" -gt 0 ]; then
        echo ""
        echo "  Failed suites:"
        echo -e "$FAILED_LIST"
    fi
    echo "========================================"
    echo "  Log saved to: $LOGFILE"
    echo "========================================"

} 2>&1 | tee "$LOGFILE"

# Check the log for failures (the subshell above doesn't propagate variables)
if grep -q 'SUITE FAILED' "$LOGFILE"; then
    exit 1
fi
exit 0
