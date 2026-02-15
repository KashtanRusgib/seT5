# Testing Guidelines

## Mandate (No Uncertainty)
**TDD ONLY**: Write tests **BEFORE** code. 100% coverage. Use the built-in test harness (`tests/test_harness.h`). **FAKE CODE = FAIL**. Run `make test` always.

### Setup
- Test harness: `include/test_harness.h` (lightweight assert-based framework).
- Directory: `tests/`.
- Naming: `tests/test_<module>.c` — one test file per source module.

### Test Files
- `tests/test_trit.c` — Unit tests for trit operations (add, mul, min, max).
- `tests/test_lexer.c` — Tokenizer coverage: valid inputs, invalid chars, edge cases.
- `tests/test_codegen.c` — Bytecode generation verification.
- `tests/test_vm.c` — VM stack execution, opcode coverage.
- `tests/test_logger.c` — Log output format verification.
- `tests/test_all.c` — Runner that executes all test suites.

### Types
- **Unit**: Per function. Every public function has at least one test.
- **Integration**: Parse + Codegen + VM round-trip.
- **Regression**: Kernel-like tests for known-fixed bugs.

### CI
- Makefile: `make test` runs all, reports pass/fail counts, logs failures.
- **ENFORCE**: Agents **MUST** fix regressions before new features.

### Test Harness API
```c
#include "test_harness.h"

TEST(test_name) {
    ASSERT_EQ(actual, expected);
    ASSERT_NEQ(actual, not_expected);
    ASSERT_TRUE(condition);
    ASSERT_STR_EQ(str1, str2);
}
```

**VERIFICATION**: Coverage report in logs. Fail if <100%.
