# seT5 — Secure Embedded Ternary Microkernel 5

A ground-up rewrite of the [seL4](https://sel4.systems/) verified microkernel
in **balanced ternary logic** (Kleene K₃).  Every value — capabilities,
addresses, registers, IPC payloads — uses three states:
`{-1 (False), 0 (Unknown), +1 (True)}`.

Uninitialized data is `Unknown`, not a silent binary zero.  This eliminates
an entire class of initialization and capability-confusion vulnerabilities
*by construction*.

> **Status:** Phase 5 Complete — 407 tests passing, TBE shell operational
> **License:** GPL-2.0 (see [LICENSE](LICENSE))

---

## Table of Contents

1. [Prerequisites](#prerequisites)
2. [Quick Start](#quick-start)
3. [Build Guide](#build-guide)
4. [Development Phases](#development-phases)
5. [Testing](#testing)
6. [TBE — Ternary Bootstrap Environment](#tbe--ternary-bootstrap-environment)
7. [Verification Process](#verification-process)
8. [Project Structure](#project-structure)
9. [Contingencies & Troubleshooting](#contingencies--troubleshooting)
10. [License & Future Plans](#license--future-plans)

---

## Prerequisites

### Required

- **Git** (2.25+) with submodule support
- **GCC** (10+) or **Clang** (14+) — C11 support required
- **GNU Make** (4.0+)

### Optional (by phase)

| Tool                  | Phase | Purpose                                   |
|-----------------------|-------|-------------------------------------------|
| Isabelle/HOL 2024     | 3+    | Formal verification of ternary proofs     |
| Icarus Verilog / Yosys| 4+    | Verilog simulation and FPGA synthesis     |
| Python 3.10+          | 5     | Trithon interop layer                    |
| QEMU (patched)        | 3+    | Ternary noise simulation / emulation     |
| Sphinx + Doxygen      | Any   | Documentation generation                 |

### Clone & Initialize

```bash
# Clone the repository
git clone git@github.com:KashtanRusgib/seT5.git
cd seT5

# Initialize the compiler submodule (Ternary-C-compiler)
git submodule update --init --recursive

# Verify submodule is present
ls tools/compiler/src/main.c   # Should exist
cat .gitmodules                 # Should show tools/compiler entry
```

---

## Quick Start

```bash
# 1. Build the ternary compiler (submodule)
make build-compiler

# 2. Build and run seT5 kernel init (native / host testing)
make set5_native
./set5_native

# Expected output:
# seT5: initialising...
#   page0: 729 trits allocated (Unknown)
#   operand stack seeded (sp=1)
#   syscall: LOAD_BALANCE  priority=1  affinity=-1
#   trit loop: +0 +1 → wrap (2 steps)
#   Kleene AND(T, U)  = +0  (expect 0/Unknown)
#   Kleene OR (T, U)  = +1  (expect +1/True)
#   seT5: booted.

# 3. Build demos
make demos
./demo/trit_demo
./demo/trit_emu_bench
```

---

## Build Guide

### Makefile Targets

| Target                 | Description                                        |
|------------------------|----------------------------------------------------|
| `make build-compiler`  | Build the ternary compiler from `tools/compiler/` submodule |
| `make set5_native`     | Compile kernel modules natively (gcc, host testing) — 178 tests |
| `make build-set5`      | Full build: compiler + ternary bytecode output     |
| `make tbe`             | Build TBE bootstrap shell (`src/tbe_main.c`)       |
| `make test_integration`| Build integration test suite — 56 tests            |
| `make test_sel4_ternary`| Build seL4 moonshot test suite — 142 tests        |
| `make test_tbe`        | Build TBE unit test suite — 31 tests               |
| `make demos`           | Build all demo programs in `demo/`                 |
| `make clang_trit_demo` | Build multi-radix Clang demo                       |
| `make bench_unroll`    | Build SIMD unroll benchmark                        |
| `make run-native`      | Build and run the native kernel init               |
| `make test`            | Full CI pipeline — all 407+ tests                  |
| `make clean`           | Clean all build artifacts (compiler + seT5)        |
| `make all`             | Alias for `build-set5`                             |

### Compiler Submodule

The ternary compiler lives in `tools/compiler/` as a Git submodule.
It provides:

- **Parser** — tokenizes and parses ternary C dialect
- **Postfix IR** — intermediate representation in reverse Polish notation
- **Code Generator** — emits ternary VM bytecode
- **VM** — software emulator for ternary bytecode execution
- **Verilog Emitter** — synthesis target for FPGA

```bash
# Build compiler standalone (from submodule directory)
cd tools/compiler && make clean && make all

# Run compiler test suite
cd tools/compiler && make test_trit test_parser test_vm
./test_trit && ./test_parser && ./test_vm
```

### Include Paths

seT5 headers are in `include/set5/` and the compiler's headers are in
`tools/compiler/include/`.  The top-level Makefile sets both:

```
-Iinclude -Itools/compiler/include
```

Key headers:

| Header                   | Purpose                                      |
|--------------------------|----------------------------------------------|
| `set5/trit.h`            | Core trit type, Kleene AND/OR/NOT, SIMD      |
| `set5/trit_type.h`       | Range-checked construction, fault flags      |
| `set5/trit_cast.h`       | Bool↔trit embed/project, int narrowing       |
| `set5/trit_emu.h`        | 2-bit packed encoding, bulk ops, registers   |
| `set5/memory.h`          | Tryte-aligned page allocator                 |
| `set5/ipc.h`             | Synchronous endpoints, async notifications   |
| `set5/scheduler.h`       | Trit-priority scheduling                     |
| `set5/syscall.h`         | Syscall dispatch ABI (14 syscalls)           |
| `set5/multiradix.h`      | DOT_TRIT, FFT_STEP, RADIX_CONV, load bal.   |
| `set5/wcet.h`            | WCET probe telemetry                         |
| `set5/qemu_trit.h`       | QEMU noise injection for testing             |
| `set5/sel4_ternary.h`    | Full seL4 kernel object model (THE MOONSHOT) |
| `set5/posix.h`           | POSIX compatibility / translation layer      |
| `set5/dev_trit.h`        | `/dev/trit` device driver ioctls             |
| `set5/tbe_shell.h`       | TBE shell command definitions                |
| `set5.h` (compiler)      | Legacy syscall ABI, capability structs       |

---

## Development Phases

### Phase 1: Architecture Refinement — DONE

**Goal:** Define the complete ISA in documentation; validate compatibility
with the compiler submodule.

- [x] Define trit encoding (scalar + packed) in `trit.h` / `trit_emu.h`
- [x] Document Kleene lattice ops with formal proofs (`TritKleene.thy`)
- [x] Create `ARCHITECTURE.md` with full ISA, memory model, syscalls
- [x] Integrate compiler submodule into top-level Makefile
- [x] Implement `src/init.c` kernel bootstrap
- [x] Complete ISA opcode table with variable tryte widths
- [x] Document hardware alignment (Huawei, Samsung, memristive)

### Phase 2: Core Implementation — DONE

**Goal:** Implement kernel modules in C — boot, memory manager, IPC,
scheduler.

- [x] Memory manager: tryte-aligned page allocator with Unknown-init (`memory.h`, `src/memory.c`)
- [x] Capability table: grant/revoke with monotonic rights narrowing (`syscall.h`, `src/syscall.c`)
- [x] IPC: synchronous endpoints + async notifications (`ipc.h`, `src/ipc.c`)
- [x] Scheduler: trit-priority (−1/0/+1) round-robin per level (`scheduler.h`, `src/scheduler.c`)
- [x] Syscall dispatch: full 14-syscall ABI (`src/syscall.c`)
- [x] Multi-radix engine: FFT_STEP, DOT_TRIT, RADIX_CONV (`multiradix.h`, `src/multiradix.c`)

### Phase 3: Verification & Testing — DONE

**Goal:** Extend Isabelle/HOL theories; run comprehensive test suites.

- [x] `TritKleene.thy` — Kleene lattice laws proven
- [x] `TritOps.thy` — Distributivity, propagation active
- [x] Unit tests for all kernel modules — **178 tests PASS** (`make set5_native`)
- [x] Integration tests (56 tests PASS): memory → IPC → cap → sched → multiradix → WCET
- [x] seL4 moonshot validation (142 tests PASS): all 11 kernel object types
- [ ] `CapSafety.thy` — capability monotonicity proof (future)
- [ ] `IPCCorrect.thy` / `MemIsolation.thy` (future)

### Phase 4: Optimizations & Extensions — DONE

**Goal:** Performance tuning, multi-radix hooks, hardware synthesis.

- [x] 4x loop unrolling in `trit_emu.h` bulk ops
- [x] Benchmark: < 5% overhead confirmed for packed Kleene SIMD
- [x] `FFT_STEP` instruction — radix-3 butterfly
- [x] `DOT_TRIT` for ternary neural network inference
- [x] Verilog ALU (`tools/compiler/hw/ternary_alu.v`)
- [x] FPGA constraint files for iCE40 and Artix-7
- [x] QEMU noise injection framework (`qemu_trit.h`)
- [x] WCET probe telemetry (`wcet.h`)

### Phase 5: Full Stack Integration — DONE

**Goal:** Build Trithon, Trit Linux compat, TBE shell, moonshot validation.

- [x] `trithon/trithon.py` — Python trit type with Kleene ops, self-test
- [x] Trit Linux: POSIX syscall translation layer (`posix.h`)
- [x] `/dev/trit` device driver stub with ioctls (`dev_trit.h`)
- [x] seL4 kernel object model — THE MOONSHOT (`sel4_ternary.h` — 1170 lines, 11 object types)
- [x] TBE bootstrap shell (`src/tbe_main.c` — 15 commands, env vars, Trithon hook)
- [x] TBE test suite — 31 tests PASS
- [x] **407 total tests passing** (178 + 56 + 142 + 31)

---

## Testing

### Running Tests

```bash
# Full CI pipeline — all 407+ tests
make test

# Individual test suites
make set5_native && ./set5_native        # 178 kernel/module tests
make test_integration && ./test_integration   # 56 integration tests
make test_sel4_ternary && ./test_sel4_ternary  # 142 moonshot tests
make test_tbe && ./test_tbe              # 31 TBE tests

# Compiler-only tests (submodule)
cd tools/compiler && bash tests/test_all.sh

# Individual compiler tests
cd tools/compiler
./test_trit && ./test_parser && ./test_vm
```

### Test Suites

| Suite               | Tests | What It Covers                                      |
|---------------------|-------|-----------------------------------------------------|
| `set5_native`       | 178   | Kernel boot, memory, IPC, scheduler, caps, multiradix, WCET, noise |
| `test_integration`  | 56    | Cross-module: mem→IPC→cap→sched→multiradix→WCET     |
| `test_sel4_ternary` | 142   | seL4 moonshot: all 11 kernel objects + POSIX layer  |
| `test_tbe`          | 31    | TBE env vars, consensus, accept_any, syscall, WCET  |
| Compiler (submodule)| 40+   | Parser, codegen, VM, type checker, linker, selfhost |
| **Total**           |**407+**| All suites passing                                  |

### Expected Results

```
$ make set5_native && ./set5_native
seT5 boot: 178 tests, 178 passed, 0 failed
seT5: ALL TESTS PASSED. Kernel operational.

$ make test_integration && ./test_integration
Integration: 56 tests, 56 passed, 0 failed
ALL INTEGRATION TESTS PASSED.

$ make test_sel4_ternary && ./test_sel4_ternary
seL4 Ternary: 142 tests, 142 passed, 0 failed
seL4 Ternary: ALL TESTS PASSED. Moonshot validated.

$ make test_tbe && ./test_tbe
TBE Tests: 31 passed, 0 failed (of 31)
```

---

## TBE — Ternary Bootstrap Environment

The TBE is seT5's minimal userspace shell — the first program that
runs after kernel boot.  Build and run interactively:

```bash
make tbe && ./tbe
```

### Commands (15)

```
tbe> help
  help, echo, env, setenv, reg, dot, syscall,
  trit_inc, trit_dec, consensus, accept_any,
  fft, wcet, trithon, exit
```

### Example Session

```
tbe> echo Hello from seT5
Hello from seT5
tbe> setenv FOO 42
Set FOO = 42 (balanced ternary)
tbe> env
Environment (3/16):
  SHELL [T] = {T}
  TRIT_MODE [T] = {TUF}
  FOO [T] = {UFFFT}
tbe> trit_inc 0
INC R00: UU_UUUUUU_UUUUUU_UUUUUU_UUUUUU_UUUUUT
tbe> consensus 0 1
CONSENSUS(R00, R01) = 0 trits agree (of 32)
tbe> trithon T&F
Trithon: T&F = F
tbe> wcet
WCET probes (6 registered):
  [0] cmd_dispatch   budget=50     max=0 ...
tbe> exit
TBE: Shutting down seT5 kernel...
```

---

## Verification Process

After each development phase, run the full verification cycle:

```bash
# 1. Clean build from scratch
make clean && make all

# 2. Run all tests
make test

# 3. Verify native kernel boots correctly
make set5_native && ./set5_native

# 4. Check for regressions (if tests fail)
git bisect start
git bisect bad HEAD
git bisect good <last-known-good-commit>
# Git bisect will binary-search for the breaking commit

# 5. Isabelle proofs (Phase 3+)
isabelle build -d proof/ -b seT5_Proofs
```

### Gate Criteria

| Transition     | Condition                                                    | Status |
|----------------|--------------------------------------------------------------|--------|
| Phase 1 → 2   | `TritKleene.thy` + `TritOps.thy` parse; all demos build     | DONE   |
| Phase 2 → 3   | Kernel init boots; memory + IPC + scheduler functional       | DONE   |
| Phase 3 → 4   | 178 kernel tests pass; proofs parse                          | DONE   |
| Phase 4 → 5   | FPGA Verilog ready; benchmarks meet perf gate; 234+ tests   | DONE   |
| Phase 5 → ∞   | Moonshot validated; TBE operational; 407+ tests              | DONE   |

---

## Project Structure

```
seT5/
├── ARCHITECTURE.md          # Full microkernel architecture (16 sections)
├── Makefile                 # Top-level build (14+ targets)
├── README.md                # This file
├── LICENSE                  # GPL-2.0
├── TODOLIST.md              # Development roadmap (all phases complete)
├── log.md                   # Development log
│
├── include/set5/            # seT5 core headers (16 headers)
│   ├── trit.h               #   Balanced trit type, Kleene ops, SIMD
│   ├── trit_type.h          #   Range-checked construction
│   ├── trit_cast.h          #   Bool↔trit casting
│   ├── trit_emu.h           #   2-bit packed emulation layer
│   ├── memory.h             #   Page allocator
│   ├── ipc.h                #   IPC endpoints/notifications
│   ├── scheduler.h          #   Trit-priority scheduler
│   ├── syscall.h            #   Syscall dispatch ABI
│   ├── multiradix.h         #   DOT_TRIT, FFT_STEP, RADIX_CONV
│   ├── wcet.h               #   WCET telemetry probes
│   ├── qemu_trit.h          #   QEMU noise injection
│   ├── sel4_ternary.h       #   seL4 kernel object model (MOONSHOT)
│   ├── posix.h              #   POSIX compatibility layer
│   ├── dev_trit.h           #   /dev/trit device driver
│   └── tbe_shell.h          #   TBE shell command definitions
│
├── src/                     # Kernel source code
│   ├── init.c               #   Kernel bootstrap (178 tests)
│   ├── memory.c             #   Page allocator implementation
│   ├── ipc.c                #   IPC implementation
│   ├── scheduler.c          #   Scheduler implementation
│   ├── syscall.c            #   Syscall dispatch implementation
│   ├── multiradix.c         #   Multi-radix engine implementation
│   └── tbe_main.c           #   TBE bootstrap shell (15 commands)
│
├── tests/                   # Test suites
│   ├── test_integration.c   #   56 integration tests
│   ├── test_sel4_ternary.c  #   142 moonshot validation tests
│   ├── test_tbe.c           #   31 TBE tests
│   └── bench_unroll.c       #   SIMD unroll benchmark
│
├── demo/                    # Demo programs
│   ├── trit_demo.c          #   Basic trit operations
│   ├── trit_type_demo.c     #   Type system demo
│   ├── trit_emu_bench.c     #   SIMD benchmark
│   └── clang_trit_demo.c    #   Multi-radix Clang demo
│
├── trithon/                 # Python Trithon interop
│   └── trithon.py           #   Python trit type + Kleene ops
│
├── proof/                   # Isabelle/HOL formal proofs
│   ├── TritKleene.thy       #   Kleene lattice laws
│   └── TritOps.thy          #   Distributivity, propagation
│
├── clang/                   # Clang compiler extensions
│   ├── include/clang/Basic/ #   Token/builtin definitions
│   └── lib/                 #   Sema checks, pragma, casting
│
├── docs/                    # Sphinx documentation
│   ├── conf.py
│   └── index.rst
│
└── tools/compiler/          # Git submodule: Ternary-C-compiler
    ├── src/                 #   Compiler source (parser, codegen, etc.)
    ├── include/             #   Compiler headers (set5.h syscall ABI)
    ├── vm/                  #   Ternary VM emulator
    ├── hw/                  #   Verilog ALU + FPGA targets
    ├── tests/               #   Compiler test suite
    └── proofs/              #   Compiler-level Isabelle proofs
```

---

## Contingencies & Troubleshooting

### Submodule not initialized

```bash
git submodule update --init --recursive
```

### Compiler build fails

```bash
cd tools/compiler
make clean && make all 2>&1 | tee build.log
# Check build.log for first error
```

### Missing headers

```bash
# Verify seT5 headers exist
ls include/set5/trit*.h

# Verify compiler headers exist
ls tools/compiler/include/set5.h

# Check include flags in Makefile
grep -- "-I" Makefile
```

### Native build fails

```bash
# Manual compile with verbose output
gcc -Wall -Wextra -Iinclude -Itools/compiler/include -o set5_native src/init.c -v
```

### Regressions after changes

```bash
# Use git bisect to find breaking commit
git bisect start
git bisect bad HEAD
git bisect good <last-good-sha>
# Build + test at each step:
make clean && make set5_native && ./set5_native
git bisect good  # or: git bisect bad
```

---

## License & Future Plans

### License

seT5 is licensed under the **GNU General Public License v2.0** (GPL-2.0).
See [LICENSE](LICENSE) for the full text.

### Future Plans

- **Next:** Isabelle/HOL proofs for capability monotonicity (`CapSafety.thy`)
- **Next:** IPC correctness and memory isolation proofs
- **Next:** Trithon CFFI bindings (Python → C trit_emu.h)
- **Next:** Trit Linux: full POSIX syscall translation + `/dev/trit` driver
- **Hardware:** FPGA synthesis on iCE40 / Artix-7
- **Research:** CNTFET ternary gates for native ternary silicon
- **Long-term:** Huawei CFET / Samsung CMOS-ternary silicon targets

### Contributing

See `tools/compiler/docs/CONTRIBUTING.md` for contribution guidelines.
All contributions must maintain the < 5% performance overhead gate and
pass the full test suite before merge.

---

*Built with balanced ternary logic — because two states were never enough.*
