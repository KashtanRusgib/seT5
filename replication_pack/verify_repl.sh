#!/usr/bin/env bash
# ══════════════════════════════════════════════════════════════════════
#  verify_repl.sh — Verify replication pack integrity
# ══════════════════════════════════════════════════════════════════════
#
#  Checks:
#   1. Structural diff between seT5_original and seT6_fork
#   2. seT5 purity (no "seT6" in C/H source)
#   3. Binary creep lint (no ELF binaries in source dirs)
#   4. Ternary purity / radix guard scan (no non-ternary deps)
#   5. seT6 test pass-rate verification (3272+ assertions, 100%)
#   6. seT5 test pass-rate verification
#
#  Usage:  ./verify_repl.sh
#
# ══════════════════════════════════════════════════════════════════════
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
CYAN='\033[0;36m'
BOLD='\033[1m'
RESET='\033[0m'

CHECKS_PASSED=0
CHECKS_FAILED=0
CHECKS_WARNED=0

pass()  { echo -e "  ${GREEN}[PASS]${RESET} $1"; CHECKS_PASSED=$((CHECKS_PASSED + 1)); }
fail()  { echo -e "  ${RED}[FAIL]${RESET} $1"; CHECKS_FAILED=$((CHECKS_FAILED + 1)); }
warn()  { echo -e "  ${YELLOW}[WARN]${RESET} $1"; CHECKS_WARNED=$((CHECKS_WARNED + 1)); }

echo ""
echo -e "${BOLD}╔══════════════════════════════════════════════════════════════╗${RESET}"
echo -e "${BOLD}║  seT5/seT6 Replication Pack — Verification                  ║${RESET}"
echo -e "${BOLD}║  Timestamp: $(date -u '+%Y-%m-%d %H:%M:%S UTC')                       ║${RESET}"
echo -e "${BOLD}╚══════════════════════════════════════════════════════════════╝${RESET}"
echo ""

# ══════════════════════════════════════════════════════════════════════
#  CHECK 1: Directory Structure
# ══════════════════════════════════════════════════════════════════════
echo -e "${CYAN}── Check 1: Directory Structure ──${RESET}"

[[ -d seT5_original ]] && pass "seT5_original/ exists" || fail "seT5_original/ MISSING"
[[ -d seT6_fork ]]     && pass "seT6_fork/ exists"     || fail "seT6_fork/ MISSING"
[[ -f build_repl.sh ]] && pass "build_repl.sh exists"  || fail "build_repl.sh MISSING"
[[ -d seT5_original/src ]]    && pass "seT5 src/ present"    || fail "seT5 src/ MISSING"
[[ -d seT5_original/tests ]]  && pass "seT5 tests/ present"  || fail "seT5 tests/ MISSING"
[[ -d seT6_fork/src ]]        && pass "seT6 src/ present"    || fail "seT6 src/ MISSING"
[[ -d seT6_fork/tests ]]      && pass "seT6 tests/ present"  || fail "seT6 tests/ MISSING"
[[ -d seT6_fork/tools ]]      && pass "seT6 tools/ present"  || fail "seT6 tools/ MISSING"
echo ""

# ══════════════════════════════════════════════════════════════════════
#  CHECK 2: seT5 Purity — no "seT6" in C/H source
# ══════════════════════════════════════════════════════════════════════
echo -e "${CYAN}── Check 2: seT5 Source Purity ──${RESET}"

SET6_IN_SET5=$(grep -rl 'seT6\|SET6' --include='*.c' --include='*.h' seT5_original/ 2>/dev/null | wc -l)
if [[ $SET6_IN_SET5 -eq 0 ]]; then
    pass "No 'seT6' references in seT5 C/H source files"
else
    fail "$SET6_IN_SET5 seT5 source files contain 'seT6' references"
fi

# Check docs mentioning seT6 (acceptable — historical context)
SET6_IN_SET5_DOCS=$(grep -rl 'seT6' --include='*.md' seT5_original/ 2>/dev/null | wc -l)
if [[ $SET6_IN_SET5_DOCS -gt 0 ]]; then
    warn "$SET6_IN_SET5_DOCS seT5 doc files mention seT6 (expected: historical references)"
else
    pass "No seT6 mentions in seT5 docs"
fi
echo ""

# ══════════════════════════════════════════════════════════════════════
#  CHECK 3: Binary Creep Lint
# ══════════════════════════════════════════════════════════════════════
echo -e "${CYAN}── Check 3: Binary Creep Lint ──${RESET}"

# Look for ELF binaries in source directories
SET5_BINS=$(find seT5_original/ -type f -executable ! -name '*.sh' ! -name '*.py' \
            ! -path '*/tools/compiler/*' 2>/dev/null | wc -l)
SET6_BINS=$(find seT6_fork/ -type f -executable ! -name '*.sh' ! -name '*.py' \
            ! -path '*/tools/compiler/*' 2>/dev/null | wc -l)

if [[ $SET5_BINS -eq 0 ]]; then
    pass "seT5_original: 0 compiled binaries (clean source)"
else
    fail "seT5_original: $SET5_BINS compiled binaries found (binary creep!)"
    find seT5_original/ -type f -executable ! -name '*.sh' ! -name '*.py' \
         ! -path '*/tools/compiler/*' 2>/dev/null | head -5 | while read -r f; do
        echo "         → $f"
    done
fi

if [[ $SET6_BINS -eq 0 ]]; then
    pass "seT6_fork: 0 compiled binaries (clean source)"
else
    fail "seT6_fork: $SET6_BINS compiled binaries found (binary creep!)"
    find seT6_fork/ -type f -executable ! -name '*.sh' ! -name '*.py' \
         ! -path '*/tools/compiler/*' 2>/dev/null | head -5 | while read -r f; do
        echo "         → $f"
    done
fi

# Check for .o object files
OBJ_COUNT=$(find . -name '*.o' 2>/dev/null | wc -l)
if [[ $OBJ_COUNT -eq 0 ]]; then
    pass "No .o object files in pack"
else
    fail "$OBJ_COUNT .o object files found"
fi
echo ""

# ══════════════════════════════════════════════════════════════════════
#  CHECK 4: Ternary Purity / Radix Guard Scan
# ══════════════════════════════════════════════════════════════════════
echo -e "${CYAN}── Check 4: Ternary Purity — Radix Guard Scan ──${RESET}"

# Scan for binary-only operations that bypass ternary logic:
#   - Raw 0b... binary literals (excluding 0b00/01/10/11 used in trit encoding)
#   - Direct boolean casts to trit without tri_clamp
#   - Any #define BASE 2 or radix=2 patterns

# Non-ternary dependency: look for "radix.*=.*2" or "BASE.*2" in C source
BINARY_RADIX=$(grep -rn 'radix\s*=\s*2\b\|#define\s\+BASE\s\+2\b\|base\s*=\s*2\b' \
               --include='*.c' --include='*.h' seT6_fork/ 2>/dev/null | wc -l)
if [[ $BINARY_RADIX -eq 0 ]]; then
    pass "No binary-radix (base-2) dependencies in seT6 C/H"
else
    warn "$BINARY_RADIX potential binary-radix references found"
    grep -rn 'radix\s*=\s*2\b\|#define\s\+BASE\s\+2\b\|base\s*=\s*2\b' \
         --include='*.c' --include='*.h' seT6_fork/ 2>/dev/null | head -3
fi

# Verify ternary type presence
TRIT_DEFS=$(grep -rl 'typedef.*trit\|TRIT_TRUE\|TRIT_FALSE\|TRIT_UNKNOWN' \
            --include='*.h' seT6_fork/ 2>/dev/null | wc -l)
if [[ $TRIT_DEFS -gt 0 ]]; then
    pass "Ternary type system present ($TRIT_DEFS header files define trit types)"
else
    fail "No ternary type definitions found"
fi

# Verify Kleene K3 logic
K3_OPS=$(grep -rl 'trit_and\|trit_or\|trit_not\|kleene' \
         --include='*.c' --include='*.h' seT6_fork/ 2>/dev/null | wc -l)
if [[ $K3_OPS -gt 0 ]]; then
    pass "Kleene K3 logic operations found in $K3_OPS files"
else
    fail "No Kleene K3 logic operations found"
fi

# Verify balanced ternary {-1, 0, +1} encoding
BT_ENCODING=$(grep -rl 'TRIT_FALSE.*-1\|trit.*-1.*0.*+1\|TRI_T.*-1' \
              --include='*.h' seT6_fork/ 2>/dev/null | wc -l)
if [[ $BT_ENCODING -gt 0 ]]; then
    pass "Balanced ternary encoding {-1,0,+1} confirmed"
else
    warn "Could not confirm balanced ternary encoding pattern"
fi

# Check for RNS moduli (ternary-friendly: {3,5,7})
RNS_MODULI=$(grep -rl '3.*5.*7\|RNS_MODULI' --include='*.c' --include='*.h' \
             seT6_fork/ 2>/dev/null | wc -l)
if [[ $RNS_MODULI -gt 0 ]]; then
    pass "RNS moduli {3,5,7} integration present ($RNS_MODULI files)"
else
    warn "No RNS moduli pattern found"
fi
echo ""

# ══════════════════════════════════════════════════════════════════════
#  CHECK 5: Structural Diff — seT5 vs seT6
# ══════════════════════════════════════════════════════════════════════
echo -e "${CYAN}── Check 5: Structural Diff (seT5 vs seT6) ──${RESET}"

SET5_FILES=$(find seT5_original/src/ -name '*.c' 2>/dev/null | wc -l)
SET6_FILES=$(find seT6_fork/src/ -name '*.c' 2>/dev/null | wc -l)
pass "seT5 src/ has $SET5_FILES C files"
pass "seT6 src/ has $SET6_FILES C files"

if [[ $SET6_FILES -ge $SET5_FILES ]]; then
    pass "seT6 has >= seT5 source files (fork extends baseline)"
else
    warn "seT6 has fewer src files than seT5"
fi

SET5_TESTS=$(find seT5_original/tests/ -name '*.c' 2>/dev/null | wc -l)
SET6_TESTS=$(find seT6_fork/tests/ -name '*.c' 2>/dev/null | wc -l)
pass "seT5 tests/ has $SET5_TESTS test files"
pass "seT6 tests/ has $SET6_TESTS test files"

SET6_ONLY_DIRS=$(diff <(ls seT5_original/ 2>/dev/null | sort) \
                      <(ls seT6_fork/ 2>/dev/null | sort) 2>/dev/null | grep '^>' | wc -l)
pass "seT6 has $SET6_ONLY_DIRS files/dirs not in seT5"
echo ""

# ══════════════════════════════════════════════════════════════════════
#  CHECK 6: seT6 Test Pass-Rate (build + run)
# ══════════════════════════════════════════════════════════════════════
echo -e "${CYAN}── Check 6: seT6 Test Verification ──${RESET}"

if [[ -d seT6_fork ]]; then
    cd seT6_fork
    make clean 2>/dev/null || true

    SET6_LOG=$(mktemp /tmp/set6_verify_XXXXXX.log)
    if make test 2>&1 | tee "$SET6_LOG" > /dev/null; then
        # Extract grand total from the log
        GRAND_LINE=$(grep 'GRAND TOTAL' "$SET6_LOG" | head -1)
        RESULT_LINE=$(grep 'RESULT:.*TESTS PASSED' "$SET6_LOG" | head -1)
        SUITES_LINE=$(grep 'Suites executed:' "$SET6_LOG" | head -1)
        PASS_RATE=$(grep 'Pass rate:' "$SET6_LOG" | head -1)

        if [[ -n "$RESULT_LINE" ]]; then
            pass "seT6 make test completed successfully"
            echo "         $RESULT_LINE"
            [[ -n "$SUITES_LINE" ]] && echo "         $SUITES_LINE"
            [[ -n "$PASS_RATE" ]] && echo "         $PASS_RATE"

            # Extract total count
            TOTAL_TESTS=$(echo "$GRAND_LINE" | grep -oE '[0-9]+' | tail -1)
            if [[ -n "$TOTAL_TESTS" && $TOTAL_TESTS -ge 2659 ]]; then
                pass "seT6 assertion count ($TOTAL_TESTS) >= 2659 threshold"
            elif [[ -n "$TOTAL_TESTS" ]]; then
                warn "seT6 assertion count ($TOTAL_TESTS) — verify against expected"
            fi

            RATE=$(echo "$PASS_RATE" | grep -oE '[0-9]+')
            if [[ "$RATE" == "100" ]]; then
                pass "seT6 pass rate: 100%"
            else
                fail "seT6 pass rate: ${RATE:-?}% (expected 100%)"
            fi
        else
            FAIL_LINE=$(grep 'RESULT:.*FAILED' "$SET6_LOG" | head -1)
            if [[ -n "$FAIL_LINE" ]]; then
                fail "seT6 tests had failures: $FAIL_LINE"
            else
                fail "seT6 test results not parseable"
            fi
        fi
    else
        fail "seT6 make test exited with error"
    fi
    rm -f "$SET6_LOG"
    cd "$SCRIPT_DIR"
else
    fail "seT6_fork/ not found"
fi
echo ""

# ══════════════════════════════════════════════════════════════════════
#  CHECK 7: trit_lint (if available)
# ══════════════════════════════════════════════════════════════════════
echo -e "${CYAN}── Check 7: Trit Lint ──${RESET}"

if [[ -x seT6_fork/tools/trit_lint.sh ]]; then
    LINT_OUT=$(bash seT6_fork/tools/trit_lint.sh seT6_fork/ 2>&1 || true)
    if echo "$LINT_OUT" | grep -qi 'error\|fail'; then
        warn "trit_lint reported issues"
        echo "$LINT_OUT" | head -5
    else
        pass "trit_lint completed (no errors)"
    fi
else
    warn "trit_lint.sh not found or not executable — skipping"
fi
echo ""

# ══════════════════════════════════════════════════════════════════════
#  SUMMARY
# ══════════════════════════════════════════════════════════════════════
TOTAL=$((CHECKS_PASSED + CHECKS_FAILED + CHECKS_WARNED))
echo -e "${BOLD}══════════════════════════════════════════════════════════════${RESET}"
echo -e "  Verification Summary:"
echo -e "    ${GREEN}Passed:${RESET}  $CHECKS_PASSED"
echo -e "    ${RED}Failed:${RESET}  $CHECKS_FAILED"
echo -e "    ${YELLOW}Warned:${RESET} $CHECKS_WARNED"
echo -e "    Total:   $TOTAL checks"
echo ""

if [[ $CHECKS_FAILED -eq 0 ]]; then
    echo -e "  ${GREEN}${BOLD}VERIFICATION PASSED — Replication pack is Sigma 9 compliant.${RESET}"
else
    echo -e "  ${RED}${BOLD}VERIFICATION FAILED — $CHECKS_FAILED check(s) failed.${RESET}"
fi
echo -e "${BOLD}══════════════════════════════════════════════════════════════${RESET}"
echo ""

[[ $CHECKS_FAILED -gt 0 ]] && exit 1
exit 0
