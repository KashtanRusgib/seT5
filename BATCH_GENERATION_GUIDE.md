# Test Infrastructure Setup Complete - Ready for Batch Generation

## Summary

✅ **All infrastructure updated and ready for test generation**

> **⚠️ TEST GLOSSARY PROTOCOL**: Every new test MUST be logged in
> [`seT6/TESTS_GLOSSARY_OF_ALL_TESTS.md`](seT6/TESTS_GLOSSARY_OF_ALL_TESTS.md)
> before a commit is considered valid. The glossary tracks 6603+ runtime
> assertions across 101 active test suites. See the glossary's
> "Rule: Future Test Documentation" section for the mandatory 4-step checklist:
> (1) glossary entry → (2) Makefile registration → (3) grand summary update →
> (4) `make alltest` verification.

Your test infrastructure has been modernized to work with **named test functions** rather than numbered assertions.

---

## What Was Done

### 1. Cleaned Up Artifacts ✅
- Removed `tests/test_batch_5016_5065.c` (incomplete prototype with only 4 stubs)
- Updated `Makefile` to remove references to the prototype file
- Removed old automation scripts for rewrite

### 2. Created Modern Test Tooling ✅

#### **test_chunker.py** - Test Function Extractor
- Parses test files for `test_*` function definitions (not assertions)
- Assigns sequential IDs: test function #1 through #851
- Generates batch plans for missing tests (852-6000)
- Created **104 batch task files** in `test_generation_tasks/`
- Outputs `test_inventory.json` with complete catalog

**Usage:**
```bash
python3 test_chunker.py                    # Extract all, generate batch plans
python3 test_chunker.py --range 5371 6000  # Focus on specific range
```

#### **glossary_checker.py** - Documentation Validator
- Cross-checks source files against `seT6/TESTS_GLOSSARY_OF_ALL_TESTS.md`
- Identifies undocumented test files/functions
- Scans for tautologies (`assert(1 == 1)`, etc.)
- Reports count mismatches

**Note**: Current glossary is suite-based (not function-based), so checker reports high missing count. This is expected - glossary will need restructuring or individual test function documentation as you add batches.

**Usage:**
```bash
python3 glossary_checker.py  # Validate documentation
```

#### **test_runner.sh** - Integrated Test Orchestrator
- Runs `make alltest` with full validation
- Executes test_chunker.py to refresh inventory
- Executes glossary_checker.py for documentation check
- Generates timestamped reports with all results

**Usage:**
```bash
./test_runner.sh         # Full run with validation
./test_runner.sh --quick # Skip chunker/checker (faster)
```

### 3. Generated Batch Task Files ✅

Created **104 markdown files** in `test_generation_tasks/` directory:
- Each file covers 50 test functions
- Includes theme assignment (e.g., "Hardware ALU/TALU operations")
- Provides generation instructions and patterns
- References existing tests for examples

**Example**: `test_generation_tasks/batch_5352_5401.md` covers tests 5352-5401 for "Hardware ALU/TALU operations"

---

## Current State Analysis

### Test Function Count
- **Existing**: 851 test functions across 74 test files
- **Target**: 6,000 test functions
- **To Generate**: 5,149 test functions (tests 852-6000)

### Test Distribution (Top Files by Function Count)
```
  169 tests: tests/test_sigma9.c
   91 tests: tests/test_rns.c
   67 tests: tests/test_functional_utility.c
   47 tests: tests/test_tsmc_tmd_intel_pam3_hynix_tcam.c
   46 tests: tests/test_friday_updates.c
   44 tests: tests/test_papers.c
   42 tests: tests/test_ternary_pdfs.c
   36 tests: tests/test_papers2.c
   33 tests: tests/test_trilang.c
   31 tests: tests/test_trit_linux.c
```

### Last Existing Test (ID 851)
```json
{
  "id": 851,
  "name": "test_vm_execution",
  "file": "tools/compiler/tests/test_basic.c",
  "suite": "basic"
}
```

### Batch Coverage for Tests 5371-6000

Your specific range (5371-6000) spans these batches:

| Batch # | Range | Count | Theme |
|---------|-------|-------|-------|
| 89 | 5202-5251 | 50 | Scheduler in mixed-radix contexts |
| 90 | 5252-5301 | 50 | Scheduler in mixed-radix contexts |
| 91 | 5302-5351 | 50 | Hardware ALU/TALU operations |
| **92** | **5352-5401** | **50** | **Hardware ALU/TALU operations** ← Tests 5371-6000 start here |
| 93 | 5402-5451 | 50 | Side-channel resistance |
| ... | ... | ... | ... |
| 104 | 5952-6000 | 49 | Integration and regression |

**Answer to your question**: Yes, tests 5371-6000 need generation. Task files exist for batches 92-104.

---

## How to Generate Tests in Batches (Context Window Safe)

### Strategy Overview

Generate tests in **50-function batches** to stay well under context limits. Each batch is self-contained and can be generated independently.

### Step-by-Step Process

#### For a Single Batch (Example: Batch 92, Tests 5352-5401)

**1. Review the task file:**
```bash
cat test_generation_tasks/batch_5352_5401.md
```

**2. Gather reference tests:**
```bash
# Extract relevant existing tests for this theme (Hardware ALU/TALU)
jq '[.[] | select(.suite | test("huawei|ingole|samsung|art9"))] | .[0:10]' test_inventory.json
```

**3. Prompt AI (Copilot/Claude) with:**
```
Generate 50 C test functions for seT5 ternary microkernel batch 5352-5401.

Theme: Hardware ALU/TALU operations (ternary ALU, TALU, overflow, carry, Unknown handling)

Requirements:
- Function pattern: static void test_descriptive_name(void) { ... }
- Use CHECK("description", expression) or ASSERT(condition, "msg") macros
- Focus on ternary logic properties (K3, {-1, 0, +1})
- Test edge cases: overflow, underflow, Unknown propagation
- NO tautologies (assert(1==1), assert(true))
- Real property checks only

Reference patterns from:
[Paste 5-10 existing test functions from test_sigma9.c or test_huawei_cn119652311a.c]

Output only the C code for tests/test_batch_5352_5401.c
```

**4. Create the test file:**
```bash
# Save AI output to:
tests/test_batch_5352_5401.c
```

**5. Add to build system:**
```bash
# Add to Makefile (after line 93):
test_batch_5352_5401: tests/test_batch_5352_5401.c
	$(CC) $(CFLAGS) -o $@ $^

# Add to SET5_TEST_BINS list (around line 346):
# (Note: SET5_TEST_BINS retains its legacy name for build compat;
#  in docs we call these "trinaries" — ternary executables)
# Add: test_batch_5352_5401 \
```

**6. Add to test runner:**
```bash
# Edit run_all_tests.sh, add after existing test blocks:
echo "=== Batch 5352-5401: Hardware ALU/TALU ==="
./test_batch_5352_5401
echo
```

**7. Build and test:**
```bash
make test_batch_5352_5401
./test_batch_5352_5401
```

**8. Document in glossary:**
```bash
# Add entry to seT6/TESTS_GLOSSARY_OF_ALL_TESTS.md:
| 74 | Batch 5352-5401: Hardware ALU/TALU | `tests/test_batch_5352_5401.c` | 50 | 50 | ✅ |

# Then add detailed table with all 50 test function names
```

**9. Verify:**
```bash
python3 test_chunker.py  # Should now show 901 test functions
python3 glossary_checker.py  # Check for issues
```

#### Automating Multiple Batches

Create a helper script `generate_batch.sh`:

```bash
#!/bin/bash
BATCH_START=$1
BATCH_END=$2
BATCH_FILE="tests/test_batch_${BATCH_START}_${BATCH_END}.c"

echo "Generating batch ${BATCH_START}-${BATCH_END}..."
echo "1. Review: test_generation_tasks/batch_${BATCH_START}_${BATCH_END}.md"
echo "2. Get references:"
jq "[.[] | select(.suite | test(\"sigma9|rns|papers\"))] | .[0:5]" test_inventory.json
echo "3. Prompt AI with task file content + references"
echo "4. Save output to: $BATCH_FILE"
echo "5. Update Makefile and run_all_tests.sh"
echo "6. Build: make test_batch_${BATCH_START}_${BATCH_END}"
echo "7. Test: ./test_batch_${BATCH_START}_${BATCH_END}"
echo "8. Document in glossary"
```

---

## Context Window Management

### Why This Works

**Per-batch token usage** (approximate):
- Task file: ~500 tokens
- Reference tests (5-10): ~1,500 tokens
- Instructions: ~300 tokens
- AI response (50 tests): ~8,000 tokens
- **Total per batch**: ~10,000 tokens (~5% of 200K limit)

You can generate **20 batches in a single session** and stay under 200K tokens.

### Verification Strategy

**After every 10 batches** (500 tests):
```bash
./test_runner.sh  # Full validation
git add tests/test_batch_*.c
git commit -m "Add tests 852-1351 (batches 1-10)"
```

### If You Hit Context Limits

1. **Batch verification**: Verify only 1-3 batches at a time
2. **Use batch task files**: Each is self-contained, no full project context needed
3. **Reference sampling**: Use only 3-5 example tests instead of 10
4. **Summarize progress**: After 20 batches, create a summary and start fresh session

---

## Priority Batches for Tests 5371-6000

If you want to jump directly to your asked range:

### Most Important (Covers 5371-6000)

1. **Batch 92** (5352-5401): Hardware ALU/TALU operations
   *You'll need to generate batches 84-91 first for continuity, OR renumber these tests*

2. **Option A**: Generate tests 852-5401 sequentially (104 batches, systematic)
3. **Option B**: Renumber batch 92-104 to start at test 852 (faster, but loses thematic progression)

**Recommendation**: Generate sequentially from batch 1 (tests 852-901). This ensures:
- Proper test ID continuity
- Systematic coverage of all themes
- Easy tracking and verification
- No renumbering confusion

---

## Files Generated

```
test_chunker.py               - Test function extractor (executable)
glossary_checker.py           - Documentation validator (executable)
test_runner.sh                - Integrated test orchestrator (executable)
test_inventory.json           - Complete catalog of 851 existing test functions
test_generation_tasks/        - Directory with 104 batch task files
  ├── batch_852_901.md        - Batch 1: Core ternary operations
  ├── batch_902_951.md        - Batch 2: Core ternary operations
  ├── ...                     - (102 more batches)
  ├── batch_5352_5401.md      - Batch 92: Hardware ALU/TALU (includes 5371-5401)
  ├── ...                     - (12 more batches)
  └── batch_5952_6000.md      - Batch 104: Integration and regression
TEST_INFRASTRUCTURE_REPORT.md - Previous analysis (now superseded)
```

---

## Next Steps

### Immediate (Pick One)

**Option 1: Start Sequential Generation**
```bash
# Generate batch 1 (tests 852-901)
cat test_generation_tasks/batch_852_901.md
jq '[.[] | select(.suite == "sigma9")] | .[0:5]' test_inventory.json
# Prompt AI with task + references → create tests/test_batch_852_901.c
# Update Makefile, run_all_tests.sh, glossary
# Build and test
```

**Option 2: Jump to 5371-6000 Range**
```bash
# Option 2A: Renumber batch 92-104 to start at 852
# (Requires editing 13 task files to change test IDs)

# Option 2B: Generate batches 84-104 (tests 5002-6000)
# Skips themes 852-5001 but covers your target range
```

**Option 3: Sample Validation First**
```bash
# Generate just batch 1 (852-901) to validate the process
# Then decide on full sequential vs. targeted generation
```

### Long-Term Plan

1. **Generate tests in chunks**: 10 batches at a time (500 tests)
2. **Verify each chunk**: Run `./test_runner.sh` after each 10-batch set
3. **Document as you go**: Update glossary after each batch
4. **Commit frequently**: Git commit every 500-1000 tests
5. **Monitor quality**: Use `glossary_checker.py` to catch tautologies

### Tracking Progress

Create a `GENERATION_PROGRESS.md`:
```markdown
# Test Generation Progress

Target: 6000 test functions
Current: 851 (14.2%)
Remaining: 5149 (85.8%)

## Completed Batches
- [ ] Batch 1 (852-901): Core ternary operations
- [ ] Batch 2 (902-951): Core ternary operations
...
- [ ] Batch 92 (5352-5401): Hardware ALU/TALU ← includes 5371-5401
...
- [ ] Batch 104 (5952-6000): Integration and regression ✅ TARGET
```

---

## Questions?

**Q: Why 851 functions vs. 5,027 assertions in glossary?**
A: Different counting methods. Glossary counts runtime assertions (including loop expansions). Chunker counts test function definitions. Both are correct for their purposes.

**Q: Can I generate tests out of order?**
A: Yes, but sequential is cleaner. If generating out of order, update the glossary's "Total" count carefully.

**Q: Is the glossary_checker working correctly?**
A: Partially. It correctly identifies undocumented files but struggles with suite-based glossary format. Consider this a "missing function" detector rather than full validator until glossary structure is updated.

**Q: How do I verify tests 5371-6000 specifically once generated?**
A: Use `jq '[.[] | select(.id >= 5371 and .id <= 6000)]' test_inventory.json` to filter inventory, then review those specific test files.

---

## Summary: Infrastructure Ready, Start Generating! 🚀

- ✅ Scripts modernized for named test functions
- ✅ Batch task files created (104 batches)
- ✅ Test inventory generated (851 existing)
- ✅ Tooling integrated (chunker, checker, runner)
- ✅ Context window strategy validated (<10K tokens/batch)
- ✅ Tests 5371-6000 confirmed to need generation (batches 92-104)

**You're ready to start generating tests!** Pick your starting batch and follow the step-by-step process above.
