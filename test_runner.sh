#!/bin/bash
# test_runner.sh - Comprehensive test execution and verification
# 
# Runs the full seT5/seT6 test suite using 'make alltest', validates results,
# extracts test inventory, checks documentation consistency, and generates reports.
#
# Usage:
#   ./test_runner.sh              # Full run
#   ./test_runner.sh --quick      # Skip chunker/checker analysis

set -euo pipefail

QUICK_MODE=false
if [[ "${1:-}" == "--quick" ]]; then
    QUICK_MODE=true
fi

TIMESTAMP=$(date +%Y%m%d_%H%M%S)
REPORT_FILE="test_report_${TIMESTAMP}.md"

echo "=============================================="
echo "  seT5/seT6 Test Runner with Verification"
echo "=============================================="
echo

# Step 1: Clean previous test binaries
echo "🧹 Step 1/5: Cleaning previous test binaries..."
make clean > /dev/null 2>&1 || true
rm -f test_*.log
echo "   ✅ Clean complete"
echo

# Step 2: Build and run all tests
echo "🔨 Step 2/5: Building and running all tests..."
echo "   Running: make alltest"
echo

if make alltest 2>&1 | tee test_alltest.log; then
    TEST_RESULT="PASS"
    echo
    echo "   ✅ All tests passed!"
else
    TEST_RESULT="FAIL"
    echo
    echo "   ❌ Some tests failed - see test_alltest.log"
fi
echo

# Step 3: Parse test results
echo "📊 Step 3/5: Analyzing test results..."

# Extract pass/fail counts from output
TOTAL_TESTS=$(grep -oP '\d+(?= tests run)' test_alltest.log | awk '{s+=$1} END {print s}' || echo "0")
PASSED_TESTS=$(grep -oP '\d+(?= passed)' test_alltest.log | awk '{s+=$1} END {print s}' || echo "0")
FAILED_TESTS=$(grep -oP '\d+(?= failed)' test_alltest.log | awk '{s+=$1} END {print s}' || echo "0")

# Alternative: count from grand summary if available
if [[ -f tools/test_grand_summary.sh ]]; then
    echo "   Using test_grand_summary.sh for detailed counts..."
    bash tools/test_grand_summary.sh > test_summary.log 2>&1 || true
    
    # Extract from summary
    SUMMARY_TOTAL=$(grep -oP 'Total:\s+\K\d+' test_summary.log | tail -1 || echo "$TOTAL_TESTS")
    SUMMARY_PASSED=$(grep -oP 'Passed:\s+\K\d+' test_summary.log | tail -1 || echo "$PASSED_TESTS")
    SUMMARY_FAILED=$(grep -oP 'Failed:\s+\K\d+' test_summary.log | tail -1 || echo "$FAILED_TESTS")
    
    if [[ "$SUMMARY_TOTAL" -gt "$TOTAL_TESTS" ]]; then
        TOTAL_TESTS=$SUMMARY_TOTAL
        PASSED_TESTS=$SUMMARY_PASSED
        FAILED_TESTS=$SUMMARY_FAILED
    fi
fi

echo "   Total:  $TOTAL_TESTS"
echo "   Passed: $PASSED_TESTS"
echo "   Failed: $FAILED_TESTS"
echo

# Step 4: Extract test inventory (unless quick mode)
if [[ "$QUICK_MODE" == "false" ]]; then
    echo "🔍 Step 4/5: Extracting test function inventory..."
    if python3 test_chunker.py > test_chunker.log 2>&1; then
        TEST_COUNT=$(jq 'length' test_inventory.json 2>/dev/null || echo "unknown")
        echo "   ✅ Extracted $TEST_COUNT test functions"
        echo "   See: test_inventory.json"
    else
        echo "   ⚠️  Chunker failed - see test_chunker.log"
        TEST_COUNT="error"
    fi
    echo
    
    # Step 5: Validate documentation
    echo "📖 Step 5/5: Validating test documentation..."
    if python3 glossary_checker.py > test_glossary_check.log 2>&1; then
        echo "   ✅ Documentation consistent"
        DOC_STATUS="OK"
    else
        echo "   ⚠️  Documentation issues found - see test_glossary_check.log"
        DOC_STATUS="ISSUES"
    fi
    echo
else
    echo "⏭️  Step 4/5: Skipped (quick mode)"
    echo "⏭️  Step 5/5: Skipped (quick mode)"
    TEST_COUNT="skipped"
    DOC_STATUS="skipped"
    echo
fi

# Generate report
echo "📝 Generating report: $REPORT_FILE"

cat > "$REPORT_FILE" <<EOF
# seT5/seT6 Test Execution Report

**Generated**: $(date)  
**Status**: $TEST_RESULT

## Summary

- **Total Tests Run**: $TOTAL_TESTS
- **Passed**: $PASSED_TESTS ✅
- **Failed**: $FAILED_TESTS ❌
- **Test Functions Extracted**: $TEST_COUNT
- **Documentation Status**: $DOC_STATUS

## Test Execution Log

See \`test_alltest.log\` for full output.

## Test Inventory

EOF

if [[ "$QUICK_MODE" == "false" && -f test_inventory.json ]]; then
    echo "See \`test_inventory.json\` for complete test function inventory." >> "$REPORT_FILE"
    echo >> "$REPORT_FILE"
    echo "### Test Distribution" >> "$REPORT_FILE"
    echo >> "$REPORT_FILE"
    python3 -c "
import json
with open('test_inventory.json') as f:
    tests = json.load(f)
    files = {}
    for t in tests:
        files[t['file']] = files.get(t['file'], 0) + 1
    for file, count in sorted(files.items(), key=lambda x: x[1], reverse=True)[:15]:
        print(f'- **{count}** tests in \`{file}\`')
" >> "$REPORT_FILE" 2>/dev/null || echo "Error generating distribution" >> "$REPORT_FILE"
else
    echo "Test inventory not generated (quick mode or error)." >> "$REPORT_FILE"
fi

cat >> "$REPORT_FILE" <<EOF

## Documentation Validation

EOF

if [[ "$QUICK_MODE" == "false" && -f test_glossary_check.log ]]; then
    echo '```' >> "$REPORT_FILE"
    tail -50 test_glossary_check.log >> "$REPORT_FILE"
    echo '```' >> "$REPORT_FILE"
else
    echo "Documentation check not run (quick mode or error)." >> "$REPORT_FILE"
fi

cat >> "$REPORT_FILE" <<EOF

## Artifacts

- \`test_alltest.log\`: Full test execution output
- \`test_summary.log\`: Grand summary (if generated)
- \`test_chunker.log\`: Test extraction log
- \`test_glossary_check.log\`: Documentation validation log
- \`test_inventory.json\`: Complete test function inventory

## Next Steps

EOF

if [[ "$FAILED_TESTS" -gt 0 ]]; then
    echo "1. Review failed tests in \`test_alltest.log\`" >> "$REPORT_FILE"
    echo "2. Fix failures and re-run \`./test_runner.sh\`" >> "$REPORT_FILE"
elif [[ "$DOC_STATUS" == "ISSUES" ]]; then
    echo "1. Review documentation issues in \`test_glossary_check.log\`" >> "$REPORT_FILE"
    echo "2. Update \`seT6/TESTS_GLOSSARY_OF_ALL_TESTS.md\`" >> "$REPORT_FILE"
    echo "3. Re-run \`python3 glossary_checker.py\` to verify" >> "$REPORT_FILE"
else
    echo "✅ All tests passing and documentation consistent!" >> "$REPORT_FILE"
    echo "No immediate action needed." >> "$REPORT_FILE"
fi

echo
echo "=============================================="
echo "  Test Run Complete"
echo "=============================================="
echo
echo "📄 Report: $REPORT_FILE"
echo "📊 Status: $TEST_RESULT"
echo

if [[ "$FAILED_TESTS" -gt 0 ]]; then
    exit 1
elif [[ "$DOC_STATUS" == "ISSUES" ]]; then
    exit 2
else
    exit 0
fi
