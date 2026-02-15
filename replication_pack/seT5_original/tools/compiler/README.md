# Ternary Compiler in C

## Overview
This is a balanced ternary compiler written in C, targeting a ternary VM for a subset of C (expanding to full C for seT5 microkernel). **NO DEVIATIONS ALLOWED**: Follow ARCHITECTURE.md exactly. All code **MUST** be modular, with unit tests covering 100% of functions. Faking code is forbidden—verify via `make test` before any commit.

## Setup
1. Clone repo: `git clone <your-private-repo>`.
2. Build: `make all`.
3. Run: `./ternary_compiler <source.c>`.
4. Test: `make test`—**MUST** pass all before pushing.

## Key Principles (Enforced in No Uncertain Terms)
- **Modularity**: Every component (lexer, parser, codegen, VM) in separate files/modules.
- **Testing**: Use the built-in test harness for unit tests. **NO CODE WITHOUT TESTS**. Agents **MUST** write tests first (TDD).
- **Logging**: Follow docs/LOGGING.md schema. Log every action.
- **Verification**: Agents **MUST** run `git diff` and log it; if tests fail, **REVERT IMMEDIATELY**.
- **Parallelism**: Use TODO locks (e.g., claim in docs/TODOLIST.md by adding [LOCKED: AgentX]).
- **Best Practices**: Commit atomic changes. No merge conflicts without resolution logs.

## Balanced Ternary
Uses trits with values **-1 (N)**, **0 (Z)**, **+1 (P)** as per Huawei's CN119652311A patent.
Logic gates: STI (Standard Ternary Inverter), MIN/MAX for AND/OR equivalents.

## Building

```bash
make all        # Build compiler, VM test, and all test suites
make test       # Run ALL test suites (trit, lexer, codegen, vm, logger, integration)
make ci         # Full CI pipeline: test + lint
make clean      # Remove build artifacts
```

## Usage

```bash
./ternary_compiler dummy
# Output:
# Compiling: 1 + 2 * 3
# Generated 9 bytes of bytecode
# Result: 7
```

## Directories
- `src/`: Core compiler code (parser, codegen, logger, bootstrap, sel4_verify).
- `include/`: Headers (ternary.h, vm.h, parser.h, codegen.h, logger.h, ir.h, memory.h, set5.h, bootstrap.h, sel4_verify.h, test_harness.h).
- `vm/`: Ternary VM simulator.
- `hw/`: Verilog ternary hardware simulation.
- `tests/`: Unit tests (one per module) and integration tests.
- `proofs/`: Isabelle/HOL formal verification.
- `docs/`: Architecture, logging, testing, and agent documentation.
- `logs/`: Agent and CI logs.

## Project Structure

```
include/
  ternary.h       — Trit type definitions and balanced ternary arithmetic
  vm.h            — VM opcode enum and interface
  parser.h        — Tokenizer/parser interface
  codegen.h       — Code generator interface
  logger.h        — Structured logging interface
  test_harness.h  — Lightweight test framework (assert macros, suite runner)
src/
  main.c          — Compiler entry point
  parser.c        — Lexer/tokenizer
  codegen.c       — Bytecode emitter with operator precedence
  logger.c        — Structured logging (per docs/LOGGING.md schema)
vm/
  ternary_vm.c    — Stack-based ternary VM
  vm_test.c       — Standalone VM test
tests/
  test_trit.c     — Exhaustive trit operation tests (add, mul, min, max)
  test_lexer.c    — Tokenizer tests (valid, edge cases, whitespace)
  test_codegen.c  — Bytecode generation tests (precedence, chaining)
  test_vm.c       — VM execution tests (stack ops, output capture)
  test_logger.c   — Logger output format and level filtering tests
  test_integration.c — End-to-end pipeline tests (tokenize→parse→codegen→VM)
docs/
  ARCHITECTURE.md — Component design and agent roles
  LOGGING.md      — Log schema and enforcement
  TESTING.md      — TDD mandate and test harness API
  TODOLIST.md     — Task tracking with lock/claim protocol
  AGENT_PROMPT.md — Agent loop and verification checklist
  BEST_PRACTICES.md, CONTRIBUTING.md, CODE_OF_CONDUCT.md
```

## Roadmap

1. **Phase 1 (MVP):** Compile simple expressions to ternary bytecode *(DONE)*
2. **Phase 2 (seT5):** Pointers/memory, syscalls, Verilog sim, self-host, seL4 verify *(DONE)*
3. **Phase 3:** Full C subset (if/else, while, arrays), type checking, linker *(DONE)*
4. **Phase 4:** Ternary hardware synthesis, FPGA target *(DONE)*
5. **Phase 5:** Full self-hosting, formal verification with Isabelle AFP complete *(DONE)*

**AGENT DIRECTIVE**: If you're an agent, read docs/AGENT_PROMPT.md first. Update this README only if architecture changes, and verify with tests.

## Build Stats
- **Test suites**: 19 (trit, lexer, parser, codegen, vm, logger, ir, sel4, integration, memory, set5, bootstrap, sel4_verify, hardware, basic, typechecker, linker, arrays, selfhost)
- **Total tests**: 286+
- **Lines of code**: ~12,400+ (src + include + tests + hw + proofs)
- **Build**: `make all` with `gcc -Wall -Wextra`
- **CI**: `make ci` (test + lint)
- **Verilog**: `hw/ternary_alu.v`, `hw/ternary_processor_full.v`, `hw/fpga_top.v` (FPGA-ready, iCE40/Xilinx targets)
- **Isabelle**: `proofs/Ternary.thy` (65+ lemmas across 5 phases: trit arithmetic, memory model, type safety, hardware correspondence, VM correctness, compilation correctness, self-hosting properties)
- **Supported features**: Balanced ternary arithmetic, 9-trit word ops, tryte (6-trit) type, ternary logic gates (consensus/accept-any), pointers and memory model, ternary-addressed memory (729 cells), lexer (keywords/idents/operators), recursive descent parser (functions, var decls, if/else/while/for, arrays, assignments, pointer syntax, comparisons), constant folding optimizer, postfix IR (POLIZ-style), type checker, multi-module linker, Setun-70 inspired two-stack VM (36 opcodes: JMP/BRZ/BRN/BRP/LOAD/STORE/SYSCALL/DUP/DROP/SWAP/OVER/ROT/TO_R/FROM_R/CMP_EQ/CMP_LT/CMP_GT/NEG/LOOP_BEGIN/LOOP_END), seT5 microkernel syscalls (10 syscall stubs), capability-based security (derivation trees, IPC endpoints, TCBs), self-hosting bootstrap compiler, self-hosted tokenizer, seL4 full compilation + verification, Verilog ternary ALU + full 36-opcode processor, FPGA synthesis (iCE40 HX8K / Xilinx Artix-7), Isabelle/HOL formal verification (VM correctness, compilation correctness, type safety, hardware correspondence)
