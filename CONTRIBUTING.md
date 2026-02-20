.# Contributing to seT5 / seT6

Thank you for your interest in the **seT5 ternary-first microkernel OS** and the
**seT6 Gödel Machine** self-improving runtime.  This guide explains how to
contribute code, tests, documentation, and research.

---

## Table of Contents

1. [Quick Start](#quick-start)
2. [Code Style](#code-style)
3. [Commit Conventions](#commit-conventions)
4. [Test Requirements (Sigma Gate)](#test-requirements-sigma-gate)
5. [Adding Tests](#adding-tests)
6. [Crown Jewel Immutability](#crown-jewel-immutability)
7. [Gödel Machine / RSI Integration](#gödel-machine--rsi-integration)
8. [Documentation](#documentation)
9. [Copilot / AI Prompt Templates](#copilot--ai-prompt-templates)
10. [License](#license)

---

## Quick Start

```bash
# Clone
git clone https://github.com/KashtanRusgib/seT5.git
cd seT5

# Build everything and run the full test suite
make alltest

# Expected output (current baseline):
#   RESULT: ALL 6253 TESTS PASSED across 94 suites
#   Pass rate: 100%
```

Requirements: GCC (C99), Python 3.11+, `make`, Linux (Ubuntu 22.04+ recommended).
The included `.devcontainer/` configuration provides a ready-to-use GitHub Codespace.

---

## Code Style

| Rule | Detail |
|------|--------|
| Language | C99 (`-std=c99 -Wall -Wextra -Wpedantic -Werror`) |
| Trit-first | Use `trit` (from `set5/trit.h`), never raw `int` for ternary values |
| Balanced ternary | `TRIT_FALSE = -1`, `TRIT_UNKNOWN = 0`, `TRIT_TRUE = +1` |
| Kleene K₃ | `trit_and()` = min, `trit_or()` = max, `trit_not()` = negate |
| UNKNOWN propagation | Never silently collapse `UNKNOWN` to `FALSE` or `TRUE` |
| Headers | One declaration per line; prototypes in `include/set5/*.h` |
| Naming | `snake_case` for functions/variables, `UPPER_CASE` for macros |
| Max line width | 100 characters (soft), 120 characters (hard) |

---

## Commit Conventions

Format: `<scope>: <concise summary>`

Examples:
- `vm: add OP_PACK64 SIMD opcode`
- `tests: batch 6702-6751 ternary state machine`
- `docs: update TERNARY_WORLD_ROADMAP Phase 2`
- `rsi: trit guard bounds for mutation proposals`

Sigma-level milestones use: `Sigma N: XXXX tests, YY suites, 100% pass rate`

Every commit **must** pass `make alltest` with 0 failures before pushing.

---

## Test Requirements (Sigma Gate)

The project maintains a **Sigma quality gate**: every push must achieve
**100% pass rate** across all suites.

> **⚠️ TEST GLOSSARY PROTOCOL**: Every new test MUST be logged in
> [`seT6/TESTS_GLOSSARY_OF_ALL_TESTS.md`](seT6/TESTS_GLOSSARY_OF_ALL_TESTS.md)
> before a commit is considered valid. The glossary tracks 6603+ runtime
> assertions across 101 active test suites. See the glossary's
> "Rule: Future Test Documentation" section for the mandatory 4-step checklist:
> (1) glossary entry → (2) Makefile registration → (3) grand summary update →
> (4) `make alltest` verification.

```bash
# Full suite (recommended before every push)
make alltest

# Quick single-suite check
make test_batch_6702_6751 && ./test_batch_6702_6751

# ASan + UBSan memory-safety gate
make test-asan
```

Current baseline: **6253 assertions, 94 suites, 100% pass rate**.

---

## Adding Tests

### Batch Tests (50 tests per file)

Each batch file lives in `tests/test_batch_XXXX_YYYY.c` and contains exactly
**50** self-contained test functions.  Use the standard macros:

```c
#include <stdio.h>
#include <string.h>
#include "set5/trit.h"

#define SECTION(n) do { section_name = (n); } while(0)
#define TEST(d)    do { test_count++; current_test = (d); } while(0)
#define ASSERT(c, m) do { \
    if (!(c)) { \
        printf("  FAIL [%d]: %s — %s (line %d)\n", \
               test_count, current_test, m, __LINE__); \
        fail_count++; return; \
    } \
} while(0)
#define PASS() do { pass_count++ ; } while(0)
```

After creating the file:
1. Add a build target in the `Makefile`
2. Add a `##BEGIN##` echo + run entry in `_run-test-suites`
3. Add the suite name to `tools/test_grand_summary.sh` `BATCH_DEFS`
4. Add to the `ALL_TESTS` list and `clean` target
5. Run `make alltest` and verify 100%

### Integration Tests

For tests that link against `src/*.c` modules (e.g., `test_godel_machine.c`),
add the source files to the build rule:

```makefile
test_foo: tests/test_foo.c src/foo.c
	$(CC) $(CFLAGS) -o $@ $^
```

---

## Crown Jewel Immutability

The following invariants are **immutable** and must never be weakened:

- **Kleene K₃ semantics**: `UNKNOWN` is a first-class logical value
- **Balanced ternary**: {-1, 0, +1}, not {0, 1, 2}
- **No silent binary fallback**: every code path must handle all three trit values
- **Ternary-First Bridge Protocol**: no internal binary regression — when
  interoperability with binary is needed, build outward-facing bridges and
  converters at the system boundary. Binary must never be used as an internal
  data path. See `ARCHITECTURE.md` §14A for the full mandatory protocol.
- **RSI safety bounds**: `RSI_MAX_LOOPS = 10`, trit guards on every mutation
- **Sigma gate**: 100% pass rate required for every commit

See `CROWN_JEWELS.md` for the full list of protected invariants.

---

## Gödel Machine / RSI Integration

The RSI (Recursive Self-Improvement) flywheel in `src/godel_machine.c` is
bounded and trit-guarded:

- **Max 10 iterations** per session (`RSI_MAX_LOOPS`)
- **Trit guard on every mutation**: `-1` = deny, `0` = query human, `+1` = proceed
- **Beauty threshold**: only proceed if `beauty > 0.9`
- **Session compaction** every 5 iterations

When extending the Gödel Machine:
1. Add the function to `src/godel_machine.c`
2. Add `extern` declarations in the test file
3. Write tests that verify bounds, guard semantics, and convergence
4. Ensure no mutation can bypass the trit guard

---

## Documentation

Key documents:
- `WHY_SET6.md` — philosophical foundation (ternary vs binary, Corner arguments)
- `TERNARY_WORLD_ROADMAP.md` — multi-phase deployment plan
- `RSI_OPTIMIZATION_INSTRUCTIONS.md` — RSI flywheel specifications
- `CROWN_JEWELS.md` — immutable invariants
- `TODOS.md` — tracked work items (T-001 through T-088)

When adding new research or design docs, add an entry to `DOCS_INDEX.md`.

---

## Copilot / AI Prompt Templates

When using GitHub Copilot or other AI assistants with this codebase:

**For test generation:**
> Create a batch test file `tests/test_batch_XXXX_YYYY.c` with 50 self-contained
> tests covering [TOPIC]. Use balanced ternary {-1,0,+1}, Kleene K₃ semantics,
> and the standard TEST/ASSERT/PASS macros. All tests must pass.

**For RSI extensions:**
> Add a new RSI function to `src/godel_machine.c` that [BEHAVIOR]. It must
> respect RSI_MAX_LOOPS=10, use trit_guard() on mutations, and include beauty
> threshold checks. Write corresponding tests in `tests/test_godel_machine.c`.

**For VM opcodes:**
> Add opcode OP_[NAME] to `tools/compiler/include/vm.h` and implement it in
> `tools/compiler/vm/ternary_vm.c`. Update `opcode_names[]` and add integration
> tests in `tests/test_ternary_compiler_integration.c`.

---

## License

This project is licensed under the MIT License. See `LICENSE` for details.
By contributing, you agree that your contributions will be licensed under the
same terms.
