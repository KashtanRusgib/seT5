# seT5 — Secure Embedded Ternary Microkernel 5

A ground-up rewrite of the [seL4](https://sel4.systems/) verified microkernel
in **balanced ternary logic** (Kleene K₃).  Every value — capabilities,
addresses, registers, IPC payloads — uses three states:
`{-1 (False), 0 (Unknown), +1 (True)}`.

Uninitialized data is `Unknown`, not a silent binary zero.  This eliminates
an entire class of initialization and capability-confusion vulnerabilities
*by construction*.

> **Status:** Phase 1 — Architecture Refinement & Scaffolding (active)
> **License:** GPL-2.0 (see [LICENSE](LICENSE))

---

## Table of Contents

1. [Prerequisites](#prerequisites)
2. [Quick Start](#quick-start)
3. [Build Guide](#build-guide)
4. [Development Phases](#development-phases)
5. [Testing](#testing)
6. [Verification Process](#verification-process)
7. [Project Structure](#project-structure)
8. [Contingencies & Troubleshooting](#contingencies--troubleshooting)
9. [License & Future Plans](#license--future-plans)

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

| Target            | Description                                        |
|-------------------|----------------------------------------------------|
| `make build-compiler` | Build the ternary compiler from `tools/compiler/` submodule |
| `make set5_native`    | Compile `src/init.c` natively (gcc, host testing)  |
| `make build-set5`     | Full build: compiler + ternary bytecode output     |
| `make demos`          | Build all demo programs in `demo/`                 |
| `make run-native`     | Build and run the native kernel init               |
| `make clean`          | Clean all build artifacts (compiler + seT5)        |
| `make all`            | Alias for `build-set5`                             |

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

| Header              | Purpose                                    |
|---------------------|--------------------------------------------|
| `set5/trit.h`       | Core trit type, Kleene AND/OR/NOT, SIMD    |
| `set5/trit_type.h`  | Range-checked construction, fault flags    |
| `set5/trit_cast.h`  | Bool↔trit embed/project, int narrowing     |
| `set5/trit_emu.h`   | 2-bit packed encoding, bulk ops, registers |
| `set5.h` (compiler) | Syscall ABI, capability structs            |

---

## Development Phases

### Phase 1: Architecture Refinement (Current)

**Goal:** Define the complete ISA in documentation; validate compatibility
with the compiler submodule.

- [x] Define trit encoding (scalar + packed) in `trit.h` / `trit_emu.h`
- [x] Document Kleene lattice ops with formal proofs (`TritKleene.thy`)
- [x] Create `ARCHITECTURE.md` with full ISA, memory model, syscalls
- [x] Integrate compiler submodule into top-level Makefile
- [x] Implement `src/init.c` kernel bootstrap
- [ ] Complete ISA opcode table with binary encodings
- [ ] Document variable tryte width selection criteria

**Contingency — ISA incompatible with compiler:**
Update the compiler submodule to a compatible tag:
```bash
cd tools/compiler
git fetch origin
git checkout <compatible-tag>
cd ../..
git add tools/compiler
git commit -m "Update compiler submodule to <compatible-tag>"
```

### Phase 2: Core Implementation

**Goal:** Implement kernel modules in C — boot, memory manager, IPC,
scheduler.

- [ ] Memory manager: tryte-aligned page allocator with Unknown-init
- [ ] Capability table: grant/revoke with monotonic rights narrowing
- [ ] IPC: synchronous endpoints + async notifications
- [ ] Scheduler: trit-priority (−1/0/+1) round-robin per level
- [ ] Syscall dispatch: full ABI from `set5.h`

**Build & test cycle:**
```bash
make build-compiler       # Ensure compiler is current
make set5_native          # Native build for host testing
./set5_native             # Run and verify output
make build-set5           # Ternary bytecode build (when compiler supports it)
```

**Contingency — compile errors:**
1. Check `#include` paths: ensure `-Iinclude -Itools/compiler/include`
2. Verify trit library headers: `ls include/set5/trit*.h`
3. Check for missing functions: `grep -r "undefined reference" build.log`
4. If compiler submodule is stale: `git submodule update --remote tools/compiler`

### Phase 3: Verification & Testing

**Goal:** Extend Isabelle/HOL theories for capability safety, IPC
correctness, and memory isolation.  Run full test suite.

- [ ] `CapSafety.thy` — capability monotonicity proof
- [ ] `IPCCorrect.thy` — IPC message delivery correctness
- [ ] `MemIsolation.thy` — no cross-process data leakage
- [ ] Unit tests for all kernel modules (100+ tests)
- [ ] Integration tests: boot → alloc → IPC → shutdown

**Build & test:**
```bash
make clean && make all && make test
# Run Isabelle proofs (requires Isabelle/HOL 2024):
isabelle build -d proof/ -b seT5_Proofs
```

**Contingency — tests fail:**
1. Debug with VM emulator: `cd tools/compiler && ./vm_test`
2. Add logging: `#include "logger.h"` and use `log_debug()` / `log_info()`
3. Check edge cases: Unknown propagation in AND/OR chains
4. Run individual test: `./test_trit` or `./test_vm` for isolation

### Phase 4: Optimizations & Extensions

**Goal:** Performance tuning (loop unrolling, SIMD), multi-radix hooks
(FFT, dot product), and hardware synthesis.

- [ ] 4x loop unrolling in `trit_emu.h` bulk ops (already started)
- [ ] Benchmark: confirm < 5% overhead vs binary AND (perf gate)
- [ ] `FFT_STEP` instruction implementation
- [ ] `DOT_TRIT` for ternary neural network inference
- [ ] Verilog synthesis: `ternary_alu.v` → FPGA bitstream

**Contingency — hardware synthesis failures:**
1. Check constraint files: `tools/compiler/hw/fpga_constraints.pcf` (iCE40)
   or `fpga_constraints.xdc` (Artix-7)
2. Simplify ALU: disable multi-radix ops, synthesize core-only
3. Run simulation first: `iverilog -o sim tools/compiler/hw/ternary_alu.v
   tools/compiler/hw/ternary_tb.v && vvp sim`

### Phase 5: Full Stack Integration

**Goal:** Build Trithon (Python interop), Trit Linux compatibility layer,
and prepare for hardware ports.

- [ ] `trithon` Python package: CFFI bindings to `trit_emu.h`
- [ ] NumPy-compatible ternary arrays
- [ ] Trit Linux: POSIX syscall translation layer
- [ ] `/dev/trit` device driver stub
- [ ] End-to-end: Python → Trithon → seT5 kernel → FPGA

**Contingency — version mismatches in submodule:**
```bash
# Pull latest compiler updates
cd tools/compiler
git pull origin main
cd ../..
git add tools/compiler
git commit -m "Update compiler submodule"

# If breaking changes, pin to last known good:
cd tools/compiler
git log --oneline -10       # Find good commit
git checkout <good-hash>
cd ../..
git add tools/compiler
git commit -m "Pin compiler to known-good version"
```

---

## Testing

### Running Tests

```bash
# Full test suite (compiler + seT5)
make test

# Compiler-only tests
cd tools/compiler && bash tests/test_all.sh

# Individual test suites
cd tools/compiler
./test_trit          # Trit math edge cases
./test_parser        # Parser correctness
./test_codegen       # Code generation
./test_vm            # VM execution
./test_typechecker   # Type system checks
./test_linker        # Linker integration
./test_sel4_verify   # seL4 verification stubs
./test_selfhost      # Self-hosting bootstrap
./test_arrays        # Array operations
./test_hardware      # Hardware emulation
```

### Test Categories

| Category          | Tests | What It Covers                                    |
|-------------------|-------|---------------------------------------------------|
| Boot              | 5+    | Kernel init, page allocation, stack setup         |
| Memory isolation  | 10+   | Unknown-init, no cross-page leakage              |
| IPC               | 15+   | Sync endpoints, async notifications, badges      |
| Trit math         | 30+   | Kleene AND/OR/NOT, carry, overflow, edge cases   |
| Capabilities      | 15+   | Grant/revoke monotonicity, Unknown-right denial  |
| Compiler          | 40+   | Parsing, codegen, VM, type checking, linking     |
| **Total target**  |**100+**| All suites passing                               |

### Expected Results

```
$ make test
[PASS] test_trit .............. 12/12
[PASS] test_parser ........... 8/8
[PASS] test_codegen .......... 6/6
[PASS] test_vm ............... 10/10
[PASS] test_typechecker ...... 5/5
[PASS] test_linker ........... 4/4
[PASS] test_integration ..... 7/7
...
All tests passed: 100+/100+
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

| Transition     | Condition                                                    |
|----------------|--------------------------------------------------------------|
| Phase 1 → 2   | `TritKleene.thy` + `TritOps.thy` parse; all demos build     |
| Phase 2 → 3   | Kernel init boots; memory + IPC stubs functional             |
| Phase 3 → 4   | All tests pass; Isabelle proofs discharge; < 5% overhead     |
| Phase 4 → 5   | FPGA synthesis succeeds; benchmarks meet perf gate           |

---

## Project Structure

```
seT5/
├── ARCHITECTURE.md          # Full microkernel architecture document
├── Makefile                 # Top-level build (integrates compiler submodule)
├── README.md                # This file
├── LICENSE                  # GPL-2.0
├── TODOLIST.md              # Sequential development roadmap
│
├── include/set5/            # seT5 core headers
│   ├── trit.h               #   Balanced trit type, Kleene ops, SIMD
│   ├── trit_type.h          #   Range-checked construction
│   ├── trit_cast.h          #   Bool↔trit casting
│   └── trit_emu.h           #   2-bit packed emulation layer
│
├── src/                     # Kernel source code
│   └── init.c               #   Kernel bootstrap (boot, stacks, syscalls)
│
├── demo/                    # Demo programs
│   ├── trit_demo.c          #   Basic trit operations
│   ├── trit_type_demo.c     #   Type system demo
│   └── trit_emu_bench.c     #   SIMD benchmark
│
├── proof/                   # Isabelle/HOL formal proofs
│   ├── TritKleene.thy       #   Kleene lattice laws
│   └── TritOps.thy          #   Distributivity, propagation
│
├── clang/                   # Clang compiler extensions (planned)
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

- **2026 Q1-Q2:** Complete Phase 1-2 (ISA docs + core kernel modules)
- **2026 Q3:** Phase 3 (Isabelle verification, full test suite)
- **2026 Q4:** Phase 4 (FPGA synthesis, performance optimization)
- **2027+:** Phase 5 (Trithon, Trit Linux, hardware ports)
- **Research:** CNTFET ternary gates for native ternary silicon

### Contributing

See `tools/compiler/docs/CONTRIBUTING.md` for contribution guidelines.
All contributions must maintain the < 5% performance overhead gate and
pass the full test suite before merge.

---

*Built with balanced ternary logic — because two states were never enough.*
