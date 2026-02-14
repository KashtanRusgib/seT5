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
#  Supported suite output formats:
#    A) === Name: P/T passed ===                   (Compiler sub-suites)
#    B) Name: N tests, N passed, N failed          (seT5 Boot, Integration, seL4)
#    C) === Results: P/T passed ===                (Memory Safety, Scheduler)
#    D) === Results: P passed, F failed ===        (Huawei, Samsung HALs)
#    E) Name Tests: P passed, F failed (of T)     (TBE, Trit Linux)
#    F)   Total: N / Passed: N / Failed: N         (Functional Utility)
#    G)   Results: N run, N passed, N failed       (Friday Updates)
#    H) --- Name: P passed, F failed (of T) ---   (Enhancement sub-suites)
#    I) Count individual PASSED lines              (Trithon Self-Test)
#
# ══════════════════════════════════════════════════════════════════════
set -uo pipefail

LOG="${1:?Usage: test_grand_summary.sh <logfile>}"
[[ -f "$LOG" ]] || { echo "[test_grand_summary] Error: log file not found: $LOG" >&2; exit 1; }

# ── Result accumulator arrays ─────────────────────────────────────────
declare -a SNAME=() SPASS=() SFAIL=()

add_result() {
    SNAME+=("$1")
    SPASS+=("${2:-0}")
    SFAIL+=("${3:-0}")
}

# ── Helper: extract "N passed" and "N failed" from a single line ──────
#    Works for any line containing "N passed" and "N failed" text.
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
#  1. COMPILER SUB-SUITES  (Format A)
#     Pattern: === Name: P/T passed ===
#     These lines only appear in the compiler test output.
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
fi

# ══════════════════════════════════════════════════════════════════════
#  3. INTEGRATION  (Format B)
#     Pattern: Integration: N tests, N passed, N failed
# ══════════════════════════════════════════════════════════════════════
line=$(grep '^Integration:.*passed.*failed' "$LOG" | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Integration" "$p" "$f"
fi

# ══════════════════════════════════════════════════════════════════════
#  4. seL4 TERNARY  (Format B)
#     Pattern: seL4 Ternary: N tests, N passed, N failed
# ══════════════════════════════════════════════════════════════════════
line=$(grep 'seL4 Ternary:.*passed.*failed' "$LOG" | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "seL4 Ternary" "$p" "$f"
fi

# ══════════════════════════════════════════════════════════════════════
#  5. MEMORY SAFETY  (Format C)
#     Pattern: === Results: P/T passed ===
#     Disambiguated by extracting from the Memory Safety section only.
# ══════════════════════════════════════════════════════════════════════
line=$(sed -n '/=== Memory safety test ===/,/=== Scheduler concurrency/p' "$LOG" \
       | grep 'Results:.*passed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pt "$line")"
    add_result "Memory Safety" "$p" "$f"
fi

# ══════════════════════════════════════════════════════════════════════
#  6. SCHEDULER CONCURRENCY  (Format C)
#     Pattern: === Results: P/T passed ===
#     Disambiguated by extracting from the Scheduler section only.
# ══════════════════════════════════════════════════════════════════════
line=$(sed -n '/=== Scheduler concurrency test ===/,/=== TBE tests/p' "$LOG" \
       | grep 'Results:.*passed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pt "$line")"
    add_result "Scheduler Concurrency" "$p" "$f"
fi

# ══════════════════════════════════════════════════════════════════════
#  7. TBE BOOTSTRAP  (Format E)
#     Pattern: TBE Tests: P passed, F failed (of T)
# ══════════════════════════════════════════════════════════════════════
line=$(grep 'TBE Tests:.*passed.*failed' "$LOG" | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "TBE Bootstrap" "$p" "$f"
fi

# ══════════════════════════════════════════════════════════════════════
#  8. HUAWEI CN119652311A  (Format D)
#     Pattern: === Results: P passed, F failed ===
#     Disambiguated by extracting from the Huawei section only.
# ══════════════════════════════════════════════════════════════════════
line=$(sed -n '/=== Huawei CN119652311A/,/=== Samsung US11170290B2/p' "$LOG" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Huawei CN119652311A" "$p" "$f"
fi

# ══════════════════════════════════════════════════════════════════════
#  9. SAMSUNG US11170290B2  (Format D)
#     Pattern: === Results: P passed, F failed ===
#     Disambiguated by extracting from the Samsung US section only.
# ══════════════════════════════════════════════════════════════════════
line=$(sed -n '/=== Samsung US11170290B2/,/=== Samsung CN105745888A/p' "$LOG" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Samsung US11170290B2" "$p" "$f"
fi

# ══════════════════════════════════════════════════════════════════════
# 10. SAMSUNG CN105745888A  (Format D)
#     Pattern: === Results: P passed, F failed ===
#     Disambiguated by extracting from the Samsung CN section only.
# ══════════════════════════════════════════════════════════════════════
line=$(sed -n '/=== Samsung CN105745888A/,/=== Functional utility/p' "$LOG" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Samsung CN105745888A" "$p" "$f"
fi

# ══════════════════════════════════════════════════════════════════════
# 11. FUNCTIONAL UTILITY  (Format F)
#     Pattern:   Passed: N  /  Failed: N  (multi-line)
#     Extracted from the Functional Utility section only.
# ══════════════════════════════════════════════════════════════════════
fu_block=$(sed -n '/=== Functional utility tests ===/,/=== Friday Updates/p' "$LOG")
fu_p=$(echo "$fu_block" | grep -m1 'Passed:' | grep -oE '[0-9]+' | head -1)
fu_f=$(echo "$fu_block" | grep -m1 'Failed:' | grep -oE '[0-9]+' | head -1)
if [[ -n "$fu_p" ]]; then
    add_result "Functional Utility" "${fu_p}" "${fu_f:-0}"
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
fi

# ══════════════════════════════════════════════════════════════════════
# 13. TRITHON SELF-TEST  (Format I)
#     Counts individual PASSED/FAILED lines in the Trithon section.
# ══════════════════════════════════════════════════════════════════════
trithon_block=$(sed -n '/=== Trithon self-test ===/,/=== Trit Linux arch/p' "$LOG")
trithon_p=$(echo "$trithon_block" | grep -c 'PASSED' || true)
trithon_f=$(echo "$trithon_block" | grep -c 'FAILED' || true)
if [[ $trithon_p -gt 0 || $trithon_f -gt 0 ]]; then
    add_result "Trithon Self-Test" "$trithon_p" "$trithon_f"
fi

# ══════════════════════════════════════════════════════════════════════
# 14. TRIT LINUX ARCH  (Format E)
#     Pattern: Trit Linux Tests: P passed, F failed (of T)
# ══════════════════════════════════════════════════════════════════════
line=$(grep 'Trit Linux Tests:.*passed.*failed' "$LOG" | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Trit Linux Arch" "$p" "$f"
fi

# ══════════════════════════════════════════════════════════════════════
# 15-20. TRIT LINUX ENHANCEMENTS — 6 sub-suites  (Format H)
#     Pattern: --- Name: P passed, F failed (of T) ---
# ══════════════════════════════════════════════════════════════════════
while IFS= read -r line; do
    name=$(echo "$line" | sed 's/.*--- //; s/: [0-9].*//')
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Enhancement: $name" "$p" "$f"
done < <(grep -E '^\s*--- .+: [0-9]+ passed, [0-9]+ failed' "$LOG")

# ══════════════════════════════════════════════════════════════════════
#  GRAND SUMMARY TABLE
# ══════════════════════════════════════════════════════════════════════
GRAND_P=0
GRAND_F=0
COUNT=${#SNAME[@]}

# Guard: if nothing was parsed, warn and exit
if [[ $COUNT -eq 0 ]]; then
    echo ""
    echo "[test_grand_summary] WARNING: No test results found in log."
    echo ""
    exit 0
fi

echo ""
echo "================================================================"
echo "        seT5 GRAND TEST SUMMARY — ALL SUITES"
echo "================================================================"
printf "  %-3s  %-40s %7s %7s %7s\n" "#" "Suite" "Passed" "Failed" "Total"
echo "  ---  ---------------------------------------- ------- ------- -------"

for ((i=0; i<COUNT; i++)); do
    p=${SPASS[$i]}
    f=${SFAIL[$i]}
    t=$((p + f))
    GRAND_P=$((GRAND_P + p))
    GRAND_F=$((GRAND_F + f))
    printf "  %-3d  %-40s %7d %7d %7d\n" $((i+1)) "${SNAME[$i]}" "$p" "$f" "$t"
done

GRAND_T=$((GRAND_P + GRAND_F))
echo "  ---  ---------------------------------------- ------- ------- -------"
printf "       %-40s %7d %7d %7d\n" "GRAND TOTAL" "$GRAND_P" "$GRAND_F" "$GRAND_T"
echo "================================================================"

if [[ $GRAND_F -eq 0 ]]; then
    echo "  RESULT: ALL $GRAND_T TESTS PASSED"
else
    echo "  RESULT: $GRAND_F of $GRAND_T TESTS FAILED"
fi

if [[ $GRAND_T -gt 0 ]]; then
    RATE=$((GRAND_P * 100 / GRAND_T))
    echo "  Pass rate: ${RATE}%"
fi

echo "================================================================"
echo ""
