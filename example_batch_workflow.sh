#!/bin/bash
# Quick reference for generating a single test batch
# Usage: ./example_batch_workflow.sh 852 901
#
# This script shows the workflow - you'll need to manually:
# 1. Copy reference tests
# 2. Prompt AI with instructions + references
# 3. Save AI output to test file
# 4. Update build files
# 5. Verify tests pass

set -e

BATCH_START=${1:-852}
BATCH_END=${2:-901}
BATCH_NUM=$(( (BATCH_START - 852) / 50 + 1 ))

echo "======================================================"
echo "  Test Batch Generation Workflow"
echo "  Batch $BATCH_NUM: Tests $BATCH_START-$BATCH_END"
echo "======================================================"
echo

# Step 1: Review task file
echo "📖 Step 1/9: Review task file"
TASK_FILE="test_generation_tasks/batch_${BATCH_START}_${BATCH_END}.md"
if [[ -f "$TASK_FILE" ]]; then
    echo "   Theme: $(grep '^\*\*Theme\*\*:' "$TASK_FILE" | sed 's/.*: //')"
    echo "   File: $TASK_FILE"
else
    echo "   ❌ Task file not found: $TASK_FILE"
    exit 1
fi
echo

# Step 2: Get reference tests
echo "🔍 Step 2/9: Extract reference tests"
echo "   Extracting 5 relevant tests from inventory..."
jq -r "[.[] | select(.suite | test(\"sigma9|huawei|samsung\"))] | .[0:5] | .[] | \"   \(.id). \(.name) (\(.file))\"" test_inventory.json 2>/dev/null || echo "   (Run after test_inventory.json exists)"
echo

# Step 3: Read sample reference test
echo "📝 Step 3/9: View sample reference test"
echo "   Opening a sample test function for pattern reference..."
echo "   Example from tests/test_sigma9.c:"
grep -A 15 "^static void test_tstab_init" tests/test_sigma9.c 2>/dev/null | head -16 || echo "   (File not found or no match)"
echo

# Step 4: Create prompt
echo "✍️  Step 4/9: AI Prompt Template"
cat <<'PROMPT'
   Copy this prompt and fill in the [REFERENCES]:

   ---
   Generate 50 C test functions for seT5 ternary microkernel.
   
   **Batch**: ${BATCH_START}-${BATCH_END}
   **Theme**: [SEE TASK FILE]
   
   Requirements:
   - Function pattern: static void test_descriptive_name(void) { ... }
   - Use TEST("description") and ASSERT(condition, "message") macros
   - Focus on ternary logic: {-1, 0, +1}, Unknown handling, K3 properties
   - Test edge cases: overflow, underflow, Unknown propagation
   - NO tautologies: no assert(1==1), assert(true), or trivial checks
   - Real property checks only
   
   Reference patterns (use similar structure):
   [PASTE 3-5 EXAMPLE TEST FUNCTIONS HERE]
   
   Test harness pattern:
   ```c
   #define TEST(name) do { printf("  %-60s", name); tests_total++; } while(0)
   #define ASSERT(cond, msg) do { if (cond) { tests_passed++; printf("[PASS]\\n"); } else { tests_failed++; printf("[FAIL] %s\\n", msg); } } while(0)
   ```
   
   Output ONLY the C code for tests/test_batch_${BATCH_START}_${BATCH_END}.c
   Include file header, includes, harness, main(), and all 50 test functions.
   ---
PROMPT
echo

# Step 5: Create test file placeholder
echo "💾 Step 5/9: Test file location"
TEST_FILE="tests/test_batch_${BATCH_START}_${BATCH_END}.c"
echo "   Save AI output to: $TEST_FILE"
echo "   (Do not create yet - wait for AI response)"
echo

# Step 6: Update Makefile
echo "🔧 Step 6/9: Makefile updates needed"
echo "   After creating test file, add to Makefile:"
echo
echo "   1. Add build target (around line 95):"
echo "      test_batch_${BATCH_START}_${BATCH_END}: tests/test_batch_${BATCH_START}_${BATCH_END}.c"
echo "      	\$(CC) \$(CFLAGS) -o \$@ \$^"
echo
echo "   2. Add to SET5_TEST_BINS list (around line 346):"
echo "      test_batch_${BATCH_START}_${BATCH_END} \\"
echo

# Step 7: Update run_all_tests.sh
echo "🏃 Step 7/9: Test runner updates needed"
echo "   Add to run_all_tests.sh (around line 1100):"
echo
echo "   echo \"=== Batch ${BATCH_START}-${BATCH_END}: [THEME] ===\"
"./test_batch_${BATCH_START}_${BATCH_END}"
echo "   echo"
echo

# Step 8: Build and test
echo "🔨 Step 8/9: Build and execute"
echo "   make test_batch_${BATCH_START}_${BATCH_END}"
echo "   ./test_batch_${BATCH_START}_${BATCH_END}"
echo "   (Should see all tests pass)"
echo

# Step 9: Document
echo "📚 Step 9/9: Document in glossary"
echo "   Add to seT6/TESTS_GLOSSARY_OF_ALL_TESTS.md:"
echo "   - Update suite index table"
echo "   - Add new suite section with all 50 test descriptions"
echo "   - Update total counts in header"
echo

# Verification
echo "✅ Verification: Run after completion"
echo "   python3 test_chunker.py      # Should show 851 + 50 = 901 tests"
echo "   python3 glossary_checker.py  # Check documentation"
echo "   make alltest                  # Ensure no regressions"
echo

echo "======================================================"
echo "Ready to generate batch $BATCH_NUM!"
echo "Follow steps 1-9 above, then run next batch."
echo "======================================================"
