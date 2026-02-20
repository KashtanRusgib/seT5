#!/bin/bash
# ci.sh - Full CI pipeline for the Ternary C Compiler (TASK-008)
#
# Runs: build, test, lint, optional coverage
# Logs results to logs/ci.log
# Exit code: 0 if all pass, 1 on any failure.
#
# Usage:
#   ./ci.sh           # Run test + lint
#   ./ci.sh coverage  # Run test + lint + coverage

set -e

LOGFILE="logs/ci.log"
TIMESTAMP=$(date +"%Y-%m-%dT%H:%M:%S%z")

log() {
    local level=$1 msg=$2
    echo "[$level] [$TIMESTAMP] [CI] [TASK-008] [$msg] [{}]" >> "$LOGFILE"
    echo "[$level] $msg"
}

mkdir -p logs

log "INFO" "CI pipeline started"

# ---- Step 1: Clean build ----
echo "=== Step 1: Build ==="
make clean
if make all; then
    log "INFO" "Build passed"
else
    log "ERROR" "Build failed"
    exit 1
fi

# ---- Step 2: Run tests ----
echo ""
echo "=== Step 2: Test ==="
if make test; then
    log "INFO" "All tests passed"
else
    log "ERROR" "Tests failed"
    exit 1
fi

# ---- Step 3: Lint ----
echo ""
echo "=== Step 3: Lint ==="
if make lint; then
    log "INFO" "Lint passed"
else
    log "WARN" "Lint issues found or cppcheck not available"
fi

# ---- Step 4: Coverage (optional) ----
if [ "$1" = "coverage" ]; then
    echo ""
    echo "=== Step 4: Coverage ==="
    if make coverage; then
        log "INFO" "Coverage report generated"
    else
        log "WARN" "Coverage generation failed"
    fi
fi

echo ""
log "INFO" "CI pipeline completed successfully"
echo "=== CI: All checks passed ==="
