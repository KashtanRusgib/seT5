#!/usr/bin/env bash
# run_all_tests.sh — Master test runner for seT5 + Ternary-C-compiler
#
# Usage:  ./run_all_tests.sh
#
# Runs every test suite (compiler + seT5 kernel) in a single non-interactive
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
    echo "seT5 Full Test Run — $TS"
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
            test_logger test_ir test_sel4 test_integration test_memory test_set5 \
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

    # ── 2. seT5 kernel / integration tests ─────────────────────────────
    echo ""
    echo "########################################"
    echo "#  seT5 KERNEL TEST SUITES             #"
    echo "########################################"

    # Complete list of ALL seT5/seT6 kernel & module test suites.
    # ╔══════════════════════════════════════════════════════════════════╗
    # ║  IMPORTANT: When adding a new test suite, add its make target  ║
    # ║  here AND in the Makefile (_run-test-suites + SET5_TEST_BINS)  ║
    # ║  AND in seT6/TESTS_GLOSSARY_OF_ALL_TESTS.md.                  ║
    # ╚══════════════════════════════════════════════════════════════════╝
    SET5_SUITES="set5_native test_integration test_sel4_ternary \
        test_memory_safety test_scheduler_concurrency test_tbe \
        test_huawei_cn119652311a test_samsung_us11170290b2 \
        test_samsung_cn105745888a test_functional_utility \
        test_friday_updates test_trit_linux test_trit_enhancements \
        test_tsmc_tmd_intel_pam3_hynix_tcam test_ternary_database \
        test_ingole_wo2016199157a1 test_multi_radix_unit \
        test_ternary_wallace_tree test_ternary_sense_amp \
        test_tipc_compressor test_samsung_cn105745888a_correlator \
        test_ai_acceleration \
        test_fault_tolerant_network test_adversarial \
        test_ternary_reversion_guard test_modular test_ipc_secure \
        test_time test_hardening test_sigma9 test_rns test_papers \
        test_papers2 test_dlt_cntfet test_art9 test_ternary_pdfs \
        test_peirce_semiotic test_trilang test_sigma9_mcp test_hybrid_ai \
        test_stress test_godel_machine test_trit_simd_regression \
        test_binary_sentinel test_ternary_compiler_integration"

    for suite in $SET5_SUITES; do
        make "$suite" 2>&1
        if [ -x "./$suite" ]; then
            run_suite "seT5/$suite" "./$suite"
        else
            echo "  [SKIP] $suite (binary not found)"
        fi
    done

    # ── 3. Python test suites ──────────────────────────────────────────
    echo ""
    echo "########################################"
    echo "#  PYTHON TEST SUITES                  #"
    echo "########################################"
    run_suite "seT5/test_tjson" python3 tests/test_tjson.py
    run_suite "seT5/test_ternumpy" python3 tests/test_ternumpy.py

    # ── 4. Trithon (Python) self-test ──────────────────────────────────
    echo ""
    echo "########################################"
    echo "#  TRITHON SELF-TEST                   #"
    echo "########################################"
    make build-trithon-ext 2>&1
    run_suite "trithon/self-test" python3 trithon/trithon.py

    # ── 5. TernBench ───────────────────────────────────────────────────
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
