#!/bin/bash
# test_runner.sh — Automated test execution and validation script for seT5
# Runs "make alltest", checks for faked results, verifies execution, and reports mismatches.
# Integrates with CI for automated verification.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"

LOGFILE="test_log_$(date '+%y-%m-%d-%H-%M-%S').txt"

echo "Starting automated test run at $(date)" | tee "$LOGFILE"

# Run the full test suite
echo "Running make alltest..." | tee -a "$LOGFILE"
if ! make alltest >> "$LOGFILE" 2>&1; then
    echo "ERROR: make alltest failed!" | tee -a "$LOGFILE"
    exit 1
fi

echo "Test run completed. Analyzing results..." | tee -a "$LOGFILE"

# Check for potential faked results (exclude legitimate terms)
if grep -qi "fake result\|count only\|0 tests run" "$LOGFILE"; then
    echo "WARNING: Potential faked results detected in log!" | tee -a "$LOGFILE"
    exit 1
fi

# Extract test counts from log
total_run=$(grep "GRAND TOTAL" "$LOGFILE" | grep -oP "\d+" | tail -1 || echo "0")

# Count assertions in source files (rough estimate)
source_assertions=$(find tests/ -name "*.c" -exec grep -c "ASSERT_\|TEST(" {} \; | awk '{sum += $1} END {print sum}' || echo "0")

echo "Tests run: $total_run" | tee -a "$LOGFILE"
echo "Source assertions: $source_assertions" | tee -a "$LOGFILE"

# Check for mismatches
if [ "$total_run" -lt "$source_assertions" ]; then
    echo "WARNING: Fewer tests ran ($total_run) than source assertions ($source_assertions)!" | tee -a "$LOGFILE"
    exit 1
fi

# Verify no failures
if grep -q "failed [1-9]" "$LOGFILE"; then
    echo "ERROR: Test failures detected!" | tee -a "$LOGFILE"
    exit 1
fi

echo "All checks passed. Log saved to $LOGFILE" | tee -a "$LOGFILE"
echo "SUCCESS: Tests executed genuinely with $total_run total." | tee -a "$LOGFILE"

# Run chunker and checker
echo "Running test chunker..." | tee -a "$LOGFILE"
python3 test_chunker.py >> "$LOGFILE" 2>&1

echo "Running glossary checker..." | tee -a "$LOGFILE"
python3 glossary_checker.py >> "$LOGFILE" 2>&1