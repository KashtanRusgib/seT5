#!/usr/bin/env bash
# ══════════════════════════════════════════════════════════════════════
#  tools/test_grand_summary.sh — seT5 Grand Test Summary Generator
# ══════════════════════════════════════════════════════════════════════
#
#  Parses the full 'make test' log output and produces a formatted
#  grand summary table indexing EVERY test suite with individual
#  pass/fail assertion counts AND a grand total across all suites.
#
#  Usage:  bash tools/test_grand_summary.sh <logfile>
#
#  Called automatically by the 'make test' target after all suites
#  have completed.  The log file is a capture of the full test output
#  produced by 'tee' during the test run.
#
#  INTEGRITY GUARANTEES:
#  - Verifies the log contains a live-run timestamp (not cached output)
#  - Checks that ALL expected suites are present in the log
#  - Reports any MISSING suites as explicit failures
#  - Exit code 1 if any failures or missing suites
#
#  Supported suite output formats:
#    A) === Name: P/T passed ===                   (Compiler sub-suites)
#    B) Name: N tests, N passed, N failed          (seT5 Boot, Integration, seL4)
#    C) === Results: P/T passed ===                (Memory Safety, Scheduler)
#    D) === Results: P passed, F failed ===        (Huawei, Samsung HALs)
#    E) Name Tests: P passed, F failed (of T)     (TBE, Trit Linux)
#    F)   Total: N / Passed: N / Failed: N         (Functional Utility)
#    G)   Results: N run, N passed, N failed       (Friday Updates)
#    H) --- Name: P passed, F failed (of T) ---   (Enhancement sub-suites)
#    J) Trithon: N passed, M failed (of T asserts) (Trithon Self-Test)
#
# ══════════════════════════════════════════════════════════════════════
set -uo pipefail

LOG="${1:?Usage: test_grand_summary.sh <logfile>}"
[[ -f "$LOG" ]] || { echo "[test_grand_summary] Error: log file not found: $LOG" >&2; exit 1; }

# ── Result accumulator arrays ─────────────────────────────────────────
declare -a SNAME=() SPASS=() SFAIL=()
MISSING_SUITES=""

add_result() {
    SNAME+=("$1")
    SPASS+=("${2:-0}")
    SFAIL+=("${3:-0}")
}

# ── Helper: extract "N passed" and "N failed" from a single line ──────
extract_pf() {
    local line="$1"
    local p f
    p=$(echo "$line" | grep -oE '[0-9]+ passed' | grep -oE '[0-9]+' | head -1)
    f=$(echo "$line" | grep -oE '[0-9]+ failed' | grep -oE '[0-9]+' | head -1)
    echo "${p:-0} ${f:-0}"
}

# ── Helper: extract P and F from "P/T passed" fraction format ─────────
extract_pt() {
    local line="$1"
    local frac p t
    frac=$(echo "$line" | grep -oE '[0-9]+/[0-9]+' | head -1)
    p=${frac%/*}
    t=${frac#*/}
    echo "${p:-0} $(( ${t:-0} - ${p:-0} ))"
}

# ══════════════════════════════════════════════════════════════════════
#  INTEGRITY CHECK: Verify live-run timestamp is present
# ══════════════════════════════════════════════════════════════════════
if ! grep -q 'LIVE EXECUTION' "$LOG"; then
    echo ""
    echo "  [WARNING] Log does not contain LIVE EXECUTION timestamp."
    echo "            This may not be output from a fresh 'make test' run."
    echo ""
fi

# ══════════════════════════════════════════════════════════════════════
#  1. COMPILER SUB-SUITES  (Format A)
#     Pattern: === Name: P/T passed ===
# ══════════════════════════════════════════════════════════════════════
while IFS= read -r line; do
    name=$(echo "$line" | sed 's/^=== //; s/: [0-9].*//')
    read -r p f <<< "$(extract_pt "$line")"
    add_result "Compiler: $name" "$p" "$f"
done < <(grep -E '^=== .*: [0-9]+/[0-9]+ passed ===$' "$LOG" | grep -v '^=== Results:')

# ══════════════════════════════════════════════════════════════════════
#  2. seT5 BOOT (Native)  (Format B)
#     Pattern: seT5 boot: N tests, N passed, N failed
# ══════════════════════════════════════════════════════════════════════
line=$(grep 'seT5 boot:.*passed.*failed' "$LOG" | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "seT5 Boot (Native)" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - seT5 Boot (Native)\n"
fi

# ══════════════════════════════════════════════════════════════════════
#  3. INTEGRATION  (Format B)
#     Pattern: Integration: N tests, N passed, N failed
# ══════════════════════════════════════════════════════════════════════
line=$(grep '^Integration:.*passed.*failed' "$LOG" | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Integration" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Integration\n"
fi

# ══════════════════════════════════════════════════════════════════════
#  4. seL4 TERNARY  (Format B)
#     Pattern: seL4 Ternary: N tests, N passed, N failed
# ══════════════════════════════════════════════════════════════════════
line=$(grep 'seL4 Ternary:.*passed.*failed' "$LOG" | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "seL4 Ternary" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - seL4 Ternary\n"
fi

# ══════════════════════════════════════════════════════════════════════
#  5. MEMORY SAFETY  (Format C)
# ══════════════════════════════════════════════════════════════════════
line=$(sed -n '/=== Memory safety test ===/,/=== Scheduler concurrency/p' "$LOG" \
       | grep 'Results:.*passed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pt "$line")"
    add_result "Memory Safety" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Memory Safety\n"
fi

# ══════════════════════════════════════════════════════════════════════
#  6. SCHEDULER CONCURRENCY  (Format C)
# ══════════════════════════════════════════════════════════════════════
line=$(sed -n '/=== Scheduler concurrency test ===/,/=== TBE tests/p' "$LOG" \
       | grep 'Results:.*passed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pt "$line")"
    add_result "Scheduler Concurrency" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Scheduler Concurrency\n"
fi

# ══════════════════════════════════════════════════════════════════════
#  7. TBE BOOTSTRAP  (Format E)
#     Pattern: TBE Tests: P passed, F failed (of T)
# ══════════════════════════════════════════════════════════════════════
line=$(grep 'TBE Tests:.*passed.*failed' "$LOG" | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "TBE Bootstrap" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - TBE Bootstrap\n"
fi

# ══════════════════════════════════════════════════════════════════════
#  8. HUAWEI CN119652311A  (Format D)
# ══════════════════════════════════════════════════════════════════════
line=$(sed -n '/=== Huawei CN119652311A/,/=== Samsung US11170290B2/p' "$LOG" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Huawei CN119652311A" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Huawei CN119652311A\n"
fi

# ══════════════════════════════════════════════════════════════════════
#  9. SAMSUNG US11170290B2  (Format D)
# ══════════════════════════════════════════════════════════════════════
line=$(sed -n '/=== Samsung US11170290B2/,/=== Samsung CN105745888A/p' "$LOG" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Samsung US11170290B2" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Samsung US11170290B2\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 10. SAMSUNG CN105745888A  (Format D)
# ══════════════════════════════════════════════════════════════════════
line=$(sed -n '/=== Samsung CN105745888A/,/=== Functional utility/p' "$LOG" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Samsung CN105745888A" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Samsung CN105745888A\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 10b. TSMC TMD / INTEL PAM-3 / HYNIX TCAM  (Format D)
#     Pattern: === Results: P passed, F failed ===
# ══════════════════════════════════════════════════════════════════════
line=$(sed -n '/=== TSMC TMD.*Intel PAM-3.*Hynix TCAM/,$p' "$LOG" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "TSMC TMD/Intel PAM3/Hynix TCAM" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - TSMC TMD/Intel PAM3/Hynix TCAM\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 11. FUNCTIONAL UTILITY  (Format F)
#     Pattern:   Passed: N  /  Failed: N  (multi-line)
# ══════════════════════════════════════════════════════════════════════
fu_block=$(sed -n '/=== Functional utility tests ===/,/=== Friday Updates/p' "$LOG")
fu_p=$(echo "$fu_block" | grep -m1 'Passed:' | grep -oE '[0-9]+' | head -1)
fu_f=$(echo "$fu_block" | grep -m1 'Failed:' | grep -oE '[0-9]+' | head -1)
if [[ -n "$fu_p" ]]; then
    add_result "Functional Utility" "${fu_p}" "${fu_f:-0}"
else
    MISSING_SUITES="$MISSING_SUITES  - Functional Utility\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 12. FRIDAY UPDATES (STT-MRAM, T-IPC, TFS)  (Format G)
#     Pattern: Results: N run, N passed, N failed
# ══════════════════════════════════════════════════════════════════════
line=$(sed -n '/=== Friday Updates/,/=== Trithon self-test/p' "$LOG" \
       | grep 'Results:.*run.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Friday Updates (STT/IPC/TFS)" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Friday Updates\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 13. TRITHON SELF-TEST  (Format J — numeric assertion counts)
#     Pattern: Trithon: N passed, M failed (of T assertions)
#     Falls back to counting PASSED/FAILED lines if not found.
# ══════════════════════════════════════════════════════════════════════
trithon_block=$(sed -n '/=== Trithon self-test ===/,/=== Trit Linux arch/p' "$LOG")
trithon_summary=$(echo "$trithon_block" | grep -E '^Trithon: [0-9]+ passed, [0-9]+ failed' | head -1)
if [[ -n "$trithon_summary" ]]; then
    read -r p f <<< "$(extract_pf "$trithon_summary")"
    add_result "Trithon Self-Test" "$p" "$f"
else
    # Fallback: count individual PASSED/FAILED lines
    trithon_p=$(echo "$trithon_block" | grep -c 'PASSED' || true)
    trithon_f=$(echo "$trithon_block" | grep -c 'FAILED' || true)
    if [[ $trithon_p -gt 0 || $trithon_f -gt 0 ]]; then
        add_result "Trithon Self-Test" "$trithon_p" "$trithon_f"
    else
        MISSING_SUITES="$MISSING_SUITES  - Trithon Self-Test\n"
    fi
fi

# ══════════════════════════════════════════════════════════════════════
# 14. TRIT LINUX ARCH  (Format E)
#     Pattern: Trit Linux Tests: P passed, F failed (of T)
# ══════════════════════════════════════════════════════════════════════
line=$(grep 'Trit Linux Tests:.*passed.*failed' "$LOG" | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Trit Linux Arch" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Trit Linux Arch\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 15-20. TRIT LINUX ENHANCEMENTS — 6 sub-suites  (Format H)
#     Pattern: --- Name: P passed, F failed (of T) ---
# ══════════════════════════════════════════════════════════════════════
ENH_COUNT=0
while IFS= read -r line; do
    name=$(echo "$line" | sed 's/.*--- //; s/: [0-9].*//')
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Enhancement: $name" "$p" "$f"
    ENH_COUNT=$((ENH_COUNT + 1))
done < <(grep -E '^\s*--- .+: [0-9]+ passed, [0-9]+ failed' "$LOG")

# Expect exactly 6 enhancement sub-suites
if [[ $ENH_COUNT -lt 6 ]]; then
    MISSING_SUITES="$MISSING_SUITES  - Enhancement sub-suites (found $ENH_COUNT of 6)\n"
fi

# ══════════════════════════════════════════════════════════════════════
#  GRAND SUMMARY TABLE
# ══════════════════════════════════════════════════════════════════════
GRAND_P=0
GRAND_F=0
COUNT=${#SNAME[@]}

# Guard: if nothing was parsed, that is a fatal error
if [[ $COUNT -eq 0 ]]; then
    echo ""
    echo "  [FATAL] No test results found in log. Tests may not have run."
    echo ""
    exit 1
fi

echo ""
echo "╔══════════════════════════════════════════════════════════════╗"
echo "║         seT5 GRAND TEST SUMMARY — ALL SUITES               ║"
echo "╚══════════════════════════════════════════════════════════════╝"
echo ""
printf "  %-3s  %-40s %7s %7s %7s\n" "#" "Suite" "Passed" "Failed" "Total"
echo "  ---  ---------------------------------------- ------- ------- -------"

for ((i=0; i<COUNT; i++)); do
    p=${SPASS[$i]}
    f=${SFAIL[$i]}
    t=$((p + f))
    GRAND_P=$((GRAND_P + p))
    GRAND_F=$((GRAND_F + f))

    # Mark failed suites with X, passing with checkmark
    if [[ $f -gt 0 ]]; then
        marker="FAIL"
    else
        marker="ok"
    fi
    printf "  %-3d  %-40s %7d %7d %7d  %s\n" $((i+1)) "${SNAME[$i]}" "$p" "$f" "$t" "$marker"
done

GRAND_T=$((GRAND_P + GRAND_F))
echo "  ---  ---------------------------------------- ------- ------- -------"
printf "       %-40s %7d %7d %7d\n" "GRAND TOTAL" "$GRAND_P" "$GRAND_F" "$GRAND_T"
echo ""

# ── Missing suite report ─────────────────────────────────────────────
if [[ -n "$MISSING_SUITES" ]]; then
    echo "  *** MISSING SUITES (not found in log) ***"
    echo -e "$MISSING_SUITES" | while IFS= read -r mline; do
        [[ -n "$mline" ]] && echo "  $mline"
    done
    echo ""
fi

# ── Final verdict ─────────────────────────────────────────────────────
echo "================================================================"
if [[ $GRAND_F -eq 0 && -z "$MISSING_SUITES" ]]; then
    echo "  RESULT: ALL $GRAND_T TESTS PASSED across $COUNT suites"
elif [[ $GRAND_F -gt 0 ]]; then
    echo "  RESULT: $GRAND_F of $GRAND_T TESTS FAILED"
fi
if [[ -n "$MISSING_SUITES" ]]; then
    echo "  WARNING: Some expected suites did not produce results"
fi

if [[ $GRAND_T -gt 0 ]]; then
    RATE=$((GRAND_P * 100 / GRAND_T))
    echo "  Pass rate: ${RATE}%"
fi
echo "  Suites executed: $COUNT"
echo "================================================================"
echo ""

# Exit non-zero if any failures or missing suites
if [[ $GRAND_F -gt 0 || -n "$MISSING_SUITES" ]]; then
    exit 1
fi
exit 0
