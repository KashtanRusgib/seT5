#!/usr/bin/env bash
# ══════════════════════════════════════════════════════════════════════
#  build_repl.sh — Build and test both seT5 (baseline) and seT6 (fork)
# ══════════════════════════════════════════════════════════════════════
#
#  Usage:  ./build_repl.sh
#
#  Expects to be run from the replication_pack/ directory.
#  Builds each project clean, runs full test suites, reports results.
#
# ══════════════════════════════════════════════════════════════════════
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

RED='\033[0;31m'
GREEN='\033[0;32m'
CYAN='\033[0;36m'
BOLD='\033[1m'
RESET='\033[0m'

echo ""
echo -e "${BOLD}╔══════════════════════════════════════════════════════════════╗${RESET}"
echo -e "${BOLD}║  seT5/seT6 Replication Pack — Build & Test                  ║${RESET}"
echo -e "${BOLD}║  Timestamp: $(date -u '+%Y-%m-%d %H:%M:%S UTC')                       ║${RESET}"
echo -e "${BOLD}╚══════════════════════════════════════════════════════════════╝${RESET}"
echo ""

OVERALL_RC=0

# ── seT5 Baseline ─────────────────────────────────────────────────────
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${RESET}"
echo -e "${BOLD}  STEP 1: Building seT5 (Frozen Baseline)${RESET}"
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${RESET}"
echo ""

if [[ -d seT5_original ]]; then
    cd seT5_original
    echo "  [1/3] Cleaning..."
    make clean 2>/dev/null || true
    echo "  [2/3] Building..."
    make all 2>&1 | tail -5
    echo "  [3/3] Testing..."
    SET5_LOG=$(mktemp /tmp/set5_repl_XXXXXX.log)
    if make test 2>&1 | tee "$SET5_LOG" | tail -20; then
        echo -e "  ${GREEN}✓ seT5 build and test PASSED${RESET}"
    else
        echo -e "  ${RED}✗ seT5 build or test FAILED${RESET}"
        OVERALL_RC=1
    fi
    rm -f "$SET5_LOG"
    cd "$SCRIPT_DIR"
else
    echo -e "  ${RED}✗ seT5_original/ directory not found${RESET}"
    OVERALL_RC=1
fi

echo ""

# ── seT6 Fork ─────────────────────────────────────────────────────────
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${RESET}"
echo -e "${BOLD}  STEP 2: Building seT6 (Development Fork)${RESET}"
echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${RESET}"
echo ""

if [[ -d seT6_fork ]]; then
    cd seT6_fork
    echo "  [1/3] Cleaning..."
    make clean 2>/dev/null || true
    echo "  [2/3] Building..."
    make all 2>&1 | tail -5
    echo "  [3/3] Testing..."
    SET6_LOG=$(mktemp /tmp/set6_repl_XXXXXX.log)
    if make test 2>&1 | tee "$SET6_LOG" | tail -30; then
        echo -e "  ${GREEN}✓ seT6 build and test PASSED${RESET}"
    else
        echo -e "  ${RED}✗ seT6 build or test FAILED${RESET}"
        OVERALL_RC=1
    fi
    rm -f "$SET6_LOG"
    cd "$SCRIPT_DIR"
else
    echo -e "  ${RED}✗ seT6_fork/ directory not found${RESET}"
    OVERALL_RC=1
fi

echo ""

# ── Summary ───────────────────────────────────────────────────────────
echo -e "${BOLD}══════════════════════════════════════════════════════════════${RESET}"
if [[ $OVERALL_RC -eq 0 ]]; then
    echo -e "  ${GREEN}${BOLD}REPLICATION COMPLETE — Both seT5 and seT6 build and pass.${RESET}"
else
    echo -e "  ${RED}${BOLD}REPLICATION FAILED — Check output above for errors.${RESET}"
fi
echo -e "${BOLD}══════════════════════════════════════════════════════════════${RESET}"
echo ""

exit $OVERALL_RC
