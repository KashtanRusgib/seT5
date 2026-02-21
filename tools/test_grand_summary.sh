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
# ── Helper: extract only the lines of ONE named section ───────────────
# Returns lines from the first occurrence of the header line (exclusive)
# up to (but not including) the next "=== " section divider, so a
# build-failed suite can never borrow test counts from a later suite.
section() {
    local _log="$1" _header="$2"
    # Outer section banners in the log are prefixed with ##BEGIN##.
    # We start collecting after a ##BEGIN## line matching the header and
    # stop collecting when the next ##BEGIN## line appears, so inner
    # "=== Foo ===" lines emitted by the test binary never trigger a
    # premature exit.
    awk -v h="$_header" '
        /^##BEGIN##/ { if ($0 ~ h) { found=1 } else if (found) { exit }; next }
        found { print }
    ' "$_log"
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
line=$(section "$LOG" "=== TSMC TMD.*Intel PAM-3.*Hynix TCAM" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "TSMC TMD/Intel PAM3/Hynix TCAM" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - TSMC TMD/Intel PAM3/Hynix TCAM\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 10c. TERNARY DATABASE AND STORAGE LAYER  (Format D)
#     Pattern: === Results: P passed, F failed ===
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== Ternary Database and Storage Layer" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Ternary Database/Storage" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Ternary Database/Storage\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 10d. INGOLE WO2016199157A1 TALU  (Format D)
#     Pattern: === Results: P passed, F failed ===
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== Ingole WO2016199157A1 TALU" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Ingole WO2016199157A1 TALU" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Ingole WO2016199157A1 TALU\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 10e. AI ACCELERATION  (Format D)
#     Pattern: === Results: P passed, F failed ===
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== AI Acceleration tests ===" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "AI Acceleration" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - AI Acceleration\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 10f. FAULT-TOLERANT NETWORKING  (Format D)
#     Pattern: === Results: P passed, F failed ===
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== Fault-Tolerant Networking tests ===" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Fault-Tolerant Networking" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Fault-Tolerant Networking\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 10g. ADVERSARIAL / NEGATIVE-PATH  (Format D)
#     Pattern: === Results: P passed, F failed ===
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== Adversarial.*Negative-Path tests ===" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Adversarial / Negative-Path" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Adversarial / Negative-Path\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 10h. CROWN JEWEL REVERSION GUARD  (Format D)
#     Pattern: === Results: P passed, F failed ===
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== Crown Jewel Reversion Guard tests ===" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Crown Jewel Reversion Guard" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Crown Jewel Reversion Guard\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 10i. MODULAR ARCHITECTURE  (Format D)
#     Pattern: === Results: P passed, F failed ===
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== Modular Architecture tests ===" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Modular Architecture" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Modular Architecture\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 10j. IPC SECURITY  (Format D)
#     Pattern: === Results: P passed, F failed ===
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== IPC Security tests ===" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "IPC Security" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - IPC Security\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 10k. TIME SYNCHRONIZATION  (Format D)
#     Pattern: === Results: P passed, F failed ===
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== Time Synchronization tests ===" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Time Synchronization" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Time Synchronization\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 10l. HARDENING  (Format D)
#     Pattern: === Results: P passed, F failed ===
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== Hardening tests ===" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Hardening" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Hardening\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 10m. SIGMA 9 ARCHITECTURE  (Format D)
#     Pattern: === Results: P passed, F failed ===
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== Sigma 9 Architecture tests ===" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Sigma 9 Architecture" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Sigma 9 Architecture\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 10n. RESIDUE NUMBER SYSTEM  (Format D)
#     Pattern: === Results: P passed, F failed ===
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== Residue Number System tests ===" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Residue Number System" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Residue Number System\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 10o. RESEARCH PAPERS IMPLEMENTATION  (Format D)
#     Pattern: === Results: P passed, F failed ===
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== Research Papers Implementation tests ===" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Research Papers Implementation" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Research Papers Implementation\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 10p. RESEARCH PAPERS PART 2  (Format D)
#     Pattern: === Results: P passed, F failed ===
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== Research Papers Part 2 tests ===" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Research Papers Part 2" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Research Papers Part 2\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 10q. DLT CNFET INTEGRATION  (Format D)
#     Pattern: === Results: P passed, F failed ===
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== DLT CNFET Integration tests ===" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "DLT CNFET Integration" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - DLT CNFET Integration\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 10r. ART9 PIPELINE  (Format D)
#     Pattern: === Results: P passed, F failed ===
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== ART9 Pipeline tests ===" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "ART9 Pipeline" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - ART9 Pipeline\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 10s. TERNARY PDFS  (Format D)
#     Pattern: === Results: P passed, F failed ===
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== Ternary PDFs tests ===" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Ternary PDFs" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Ternary PDFs\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 10t. PEIRCE SEMIOTIC  (Format D)
#     Pattern: === Results: P passed, F failed ===
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== Peirce Semiotic tests ===" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Peirce Semiotic" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Peirce Semiotic\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 10u. TRILANG  (Format D)
#     Pattern: === Results: P passed, F failed ===
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== Trilang tests ===" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Trilang" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Trilang\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 10v. SIGMA 9 MCP  (Format D)
#     Pattern: === Results: P passed, F failed ===
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== Sigma 9 MCP tests ===" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Sigma 9 MCP" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Sigma 9 MCP\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 10w. HYBRID AI  (Format D)
#     Pattern: === Results: P passed, F failed ===
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== Hybrid AI tests ===" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Hybrid AI" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Hybrid AI\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 10x. STRESS  (Format D)
#     Pattern: === Results: P passed, F failed ===
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== Stress tests ===" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Stress" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Stress\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 10y. TJSON  (Python test - custom format)
#     Pattern: === TJSON Tests: N passed, M failed, T total ===
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== TJSON tests ===" \
       | grep -E '^=== TJSON Tests: [0-9]+ passed, [0-9]+ failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "TJSON" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - TJSON\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 10z. TER_NUMPY  (Python test - custom format)
#     Pattern: === TerNumPy Tests: N passed, M failed, T total ===
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== TerNumPy tests ===" \
       | grep -E '^=== TerNumPy Tests: [0-9]+ passed, [0-9]+ failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "TerNumPy" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - TerNumPy\n"
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
# 12.5. MULTI-RADIX UNIT  (Format F)
#     Pattern:   Total: N, Passed: N, Failed: N
# ══════════════════════════════════════════════════════════════════════
mru_block=$(sed -n '/=== Multi-Radix Unit tests ===/,/=== Ternary Wallace Tree/p' "$LOG")
mru_p=$(echo "$mru_block" | grep -m1 'Passed:' | sed 's/.*Passed: \([0-9]*\).*/\1/')
mru_f=$(echo "$mru_block" | grep -m1 'Failed:' | sed 's/.*Failed: \([0-9]*\).*/\1/')
if [[ -n "$mru_p" ]]; then
    add_result "Multi-Radix Unit" "${mru_p}" "${mru_f:-0}"
else
    MISSING_SUITES="$MISSING_SUITES  - Multi-Radix Unit\n"
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
# 21. GÖDEL MACHINE  (Format D)
#     Pattern: === Results: P passed, F failed ===
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== Gödel Machine tests ===" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -z "$line" ]]; then
    # Fallback: section header might lack the umlaut
    line=$(section "$LOG" "=== G.*del Machine tests ===" \
           | grep 'Results:.*passed.*failed' | head -1)
fi
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Gödel Machine" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Gödel Machine\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 22. SIMD REGRESSION  (Format D)
#     Pattern: === Results: P passed, F failed ===
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== SIMD Regression tests ===" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "SIMD Regression" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - SIMD Regression\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 23. BINARY SENTINEL  (Format D)
#     Pattern: === Results: P passed, F failed ===
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== Binary Sentinel tests ===" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Binary Sentinel" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Binary Sentinel\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 24. TERNARY COMPILER INTEGRATION  (Format D)
#     Pattern: === Results: P passed, F failed ===
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== Ternary Compiler Integration tests ===" \
       | grep 'Results:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Ternary Compiler Integration" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Ternary Compiler Integration\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 25. RED-TEAM TRIT LINUX IPC/NET EXPLOIT HARDENING  (Format D)
#     Pattern: Result: P passed, F failed, T total
# ══════════════════════════════════════════════════════════════════════
line=$(section "$LOG" "=== Red-Team Trit Linux IPC/Net Exploit Hardening ===" \
       | grep -E 'Result(s)?:.*passed.*failed' | head -1)
if [[ -n "$line" ]]; then
    read -r p f <<< "$(extract_pf "$line")"
    add_result "Red-Team Trit Linux IPC/Net Exploit Hardening" "$p" "$f"
else
    MISSING_SUITES="$MISSING_SUITES  - Red-Team Trit Linux IPC/Net Exploit Hardening\n"
fi

# ══════════════════════════════════════════════════════════════════════
# 26-40. BATCH TEST SUITES  (Format D — "=== Results: P/T passed, F failed ===")
#     Each batch uses a ##BEGIN##=== Batch NNNN-MMMM: Title === header
#     in the Makefile _run-test-suites section.
# ══════════════════════════════════════════════════════════════════════
BATCH_DEFS=(
    "Batch 5352-5401: Hardware ALU/TALU Operations"
    "Batch 5402-5451: Side-Channel Resistance"
    "Batch 5452-5501: Side-Channel Resistance Advanced"
    "Batch 5502-5551: Epistemic Logic and Hesitation"
    "Batch 5552-5601: Epistemic Logic and Hesitation Advanced"
    "Batch 5602-5651: Guardian Trit Mechanisms"
    "Batch 5652-5701: Guardian Trit Mechanisms Advanced"
    "Batch 5702-5751: Kleene K3 Unknown Propagation"
    "Batch 5752-5801: Multi-Radix Neural Inference"
    "Batch 5802-5851: Unknown-Safe IPC"
    "Batch 5852-5901: Curiosity Simulation"
    "Batch 5902-5951: Eudaimonic Scheduling"
    "Batch 5952-6001: Fault-Tolerant Reversion Guards"
    "Batch 6002-6051: Symbiotic AI-Human Interface"
    "Batch 6052-6101: Ternary Cryptographic Uncertainty"
    "Batch 6102-6151: PAM3 Multi-Radix Interconnect"
    "Batch 6152-6201: Godel Machine Self-Reference"
    "Batch 6202-6251: RSI Flywheel Safety"
    "Batch 6252-6301: Curiosity Gradient"
    "Batch 6302-6351: Beauty Symmetry"
    "Batch 6352-6401: Eudaimonic Optimization"
    "Batch 6402-6451: Balanced Ternary Arithmetic"
    "Batch 6452-6501: Mixed-Radix Packed64 SIMD"
    "Batch 6502-6551: Heptavint Multi-Radix Encoding"
    "Batch 6552-6601: Ternary Floating-Point Basics"
    "Batch 6602-6651: Ternary Error Correction GF3 Hamming"
    "Batch 6652-6701: Ternary Capability Access Control"
    "Batch 6702-6751: Ternary State Machine & Protocol Verification"
    "Batch 6752-6801: VM Developer Tools"
    "Batch 6802-6851: Exploit Regression"
    "Batch 6852-6901: Exploit Regression Pass #4"
)
for bdef in "${BATCH_DEFS[@]}"; do
    sec=$(section "$LOG" "=== $bdef ===")
    line=$(echo "$sec" | grep 'Results:.*passed.*failed' | head -1)
    if [[ -n "$line" ]]; then
        read -r p f <<< "$(extract_pf "$line")"
        add_result "$bdef" "$p" "$f"
    else
        # Alternate format: "Passed: N" / "Failed: N" on separate lines
        p_line=$(echo "$sec" | grep -i 'Passed:' | head -1)
        f_line=$(echo "$sec" | grep -i 'Failed:' | head -1)
        if [[ -n "$p_line" ]]; then
            p=$(echo "$p_line" | grep -oE '[0-9]+' | head -1)
            f=$(echo "$f_line" | grep -oE '[0-9]+' | head -1)
            add_result "$bdef" "${p:-0}" "${f:-0}"
        else
            MISSING_SUITES="$MISSING_SUITES  - $bdef\n"
        fi
    fi
done

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
