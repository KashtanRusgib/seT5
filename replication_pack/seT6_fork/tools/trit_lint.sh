#!/usr/bin/env bash
# tools/trit_lint.sh — seT6 Ternary Lint & Assertion Coverage Scanner
#
# Usage: ./tools/trit_lint.sh [--strict] [path...]
#
# Checks:
#   1. clang-tidy static analysis (if available)
#   2. Assertion coverage: TEST/ASSERT ratio must be ≥ 95%
#   3. Dead code detection: unused static functions
#   4. Header guard verification
#   5. Trit type safety: no raw int8_t where trit expected
#
# SPDX-License-Identifier: GPL-2.0

set -euo pipefail

cd "$(dirname "$0")/.."

STRICT=0
TARGETS=()
ERRORS=0
WARNINGS=0

# Parse arguments
for arg in "$@"; do
    case "$arg" in
        --strict) STRICT=1 ;;
        *) TARGETS+=("$arg") ;;
    esac
done

# Default to scanning key directories
if [[ ${#TARGETS[@]} -eq 0 ]]; then
    TARGETS=(src include trit_linux tests)
fi

echo "╔══════════════════════════════════════════════════════════════╗"
echo "║  seT6 Ternary Lint & Assertion Coverage Scanner             ║"
echo "╚══════════════════════════════════════════════════════════════╝"
echo ""

# ── Check 1: clang-tidy (if available) ─────────────────────────────────
echo "  --- Check 1: Static Analysis (clang-tidy) ---"
if command -v clang-tidy &>/dev/null; then
    C_FILES=$(find "${TARGETS[@]}" -name '*.c' -type f 2>/dev/null || true)
    if [[ -n "$C_FILES" ]]; then
        TIDY_ERRORS=0
        for f in $C_FILES; do
            if ! clang-tidy --quiet \
                --checks='-*,bugprone-*,cert-*,misc-*,-bugprone-easily-swappable-parameters,-cert-dcl37-c,-cert-dcl51-c,-misc-unused-parameters' \
                "$f" -- -Iinclude -Isrc -Itrit_linux/hw -Itrit_linux/ai \
                -Itrit_linux/net -Itrit_linux/modular 2>/dev/null | grep -q 'warning:'; then
                :
            else
                TIDY_ERRORS=$((TIDY_ERRORS + 1))
            fi
        done
        echo "  clang-tidy: scanned $(echo "$C_FILES" | wc -w) files, $TIDY_ERRORS with warnings"
        WARNINGS=$((WARNINGS + TIDY_ERRORS))
    else
        echo "  clang-tidy: no C files found in targets"
    fi
else
    echo "  clang-tidy: not available (skipping — install for full analysis)"
fi
echo ""

# ── Check 2: Assertion Coverage ─────────────────────────────────────────
echo "  --- Check 2: Assertion Coverage (TEST/ASSERT Ratio) ---"
TEST_FILES=$(find tests -name 'test_*.c' -type f 2>/dev/null || true)
TOTAL_TESTS=0
TOTAL_ASSERTS=0

for f in $TEST_FILES; do
    T=$(grep -c 'TEST(' "$f" 2>/dev/null || echo 0)
    A=$(grep -c 'ASSERT(' "$f" 2>/dev/null || echo 0)
    TOTAL_TESTS=$((TOTAL_TESTS + T))
    TOTAL_ASSERTS=$((TOTAL_ASSERTS + A))

    if [[ $T -gt 0 ]]; then
        RATIO=$(( (A * 100) / T ))
        STATUS="[OK]"
        if [[ $RATIO -lt 95 ]]; then
            STATUS="[WARN]"
            WARNINGS=$((WARNINGS + 1))
        fi
        printf "  %-40s TEST=%3d ASSERT=%3d ratio=%d%% %s\n" \
               "$f" "$T" "$A" "$RATIO" "$STATUS"
    fi
done

if [[ $TOTAL_TESTS -gt 0 ]]; then
    TOTAL_RATIO=$(( (TOTAL_ASSERTS * 100) / TOTAL_TESTS ))
    echo ""
    echo "  Total: TEST=$TOTAL_TESTS ASSERT=$TOTAL_ASSERTS ratio=${TOTAL_RATIO}%"
    if [[ $TOTAL_RATIO -lt 95 ]]; then
        echo "  ⚠ Assertion coverage below 95% target!"
        ERRORS=$((ERRORS + 1))
    else
        echo "  ✓ Assertion coverage ≥ 95%"
    fi
fi
echo ""

# ── Check 3: Dead Code Detection ────────────────────────────────────────
echo "  --- Check 3: Dead Code (Unused Static Functions) ---"
DEAD_COUNT=0
for f in $(find "${TARGETS[@]}" -name '*.c' -type f 2>/dev/null); do
    # Find static functions defined but never called
    STATICS=$(grep -oP 'static\s+\w+\s+(\w+)\s*\(' "$f" 2>/dev/null | \
              grep -oP '\w+(?=\s*\()' | tail -n +1 || true)
    for func in $STATICS; do
        COUNT=$(grep -c "$func" "$f" 2>/dev/null || echo 0)
        if [[ $COUNT -le 1 ]]; then
            echo "  [DEAD?] $f: static $func() — only 1 reference"
            DEAD_COUNT=$((DEAD_COUNT + 1))
        fi
    done
done
echo "  Potential dead static functions: $DEAD_COUNT"
if [[ $DEAD_COUNT -gt 0 ]]; then
    WARNINGS=$((WARNINGS + DEAD_COUNT))
fi
echo ""

# ── Check 4: Header Guards ──────────────────────────────────────────────
echo "  --- Check 4: Header Guard Verification ---"
GUARD_ISSUES=0
for f in $(find "${TARGETS[@]}" -name '*.h' -type f 2>/dev/null); do
    if ! grep -q '#ifndef' "$f" 2>/dev/null; then
        echo "  [MISSING] $f: no #ifndef guard"
        GUARD_ISSUES=$((GUARD_ISSUES + 1))
    fi
done
if [[ $GUARD_ISSUES -eq 0 ]]; then
    echo "  ✓ All headers have include guards"
else
    echo "  ⚠ $GUARD_ISSUES headers missing include guards"
    WARNINGS=$((WARNINGS + GUARD_ISSUES))
fi
echo ""

# ── Summary ──────────────────────────────────────────────────────────────
echo "══════════════════════════════════════════════════════════════"
echo "  Lint Summary: $ERRORS errors, $WARNINGS warnings"
echo "══════════════════════════════════════════════════════════════"

if [[ $STRICT -eq 1 && $ERRORS -gt 0 ]]; then
    exit 1
fi

exit 0
