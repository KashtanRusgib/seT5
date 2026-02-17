# seT6 — Secure Embedded Ternary Microkernel 6

A ground-up rewrite of the [seL4](https://sel4.systems/) verified microkernel
in **balanced ternary logic** (Kleene K₃).  Every value — capabilities,
addresses, registers, IPC payloads — uses three states:
`{-1 (False), 0 (Unknown), +1 (True)}`.

Uninitialized data is `Unknown`, not a silent binary zero.  This eliminates
an entire class of initialization and capability-confusion vulnerabilities
*by construction*.

> **Status:** Phase 9 — MEGA Patent Alignment & Sigma 9 Validation — 1841 tests passing across 30 suites
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
git clone git@github.com:KashtanRusgib/seT6.git
cd seT6

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

# 2. Build and run seT6 kernel init (native / host testing)
make set6_native
./set6_native

# Expected output:
# seT6: initialising...
#   page0: 729 trits allocated (Unknown)
#   operand stack seeded (sp=1)
#   syscall: LOAD_BALANCE  priority=1  affinity=-1
#   trit loop: +0 +1 → wrap (2 steps)
#   Kleene AND(T, U)  = +0  (expect 0/Unknown)
#   Kleene OR (T, U)  = +1  (expect +1/True)
#   seT6: booted.

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
| `make set6_native`     | Compile kernel modules natively (gcc, host testing) — 178 tests |
| `make build-set6`      | Full build: compiler + ternary bytecode output     |
| `make tbe`             | Build TBE bootstrap shell (`src/tbe_main.c`)       |
| `make test_integration`| Build integration test suite — 56 tests            |
| `make test_sel4_ternary`| Build seL4 moonshot test suite — 142 tests        |
| `make test_tbe`        | Build TBE unit test suite — 31 tests               |\n| `make test_trit_linux` | Build Trit Linux arch test suite — 98 tests        |\n| `make test_huawei_hal` | Huawei CN119652311A ternary chip HAL — 47 tests    |\n| `make test_samsung_nand`| Samsung US11170290B2 NAND inference — 60 tests    |\n| `make test_samsung_modem`| Samsung CN105745888A ternary modem — 61 tests    |
| `make demos`           | Build all demo programs in `demo/`                 |
| `make clang_trit_demo` | Build multi-radix Clang demo                       |
| `make bench_unroll`    | Build SIMD unroll benchmark                        |
| `make run-native`      | Build and run the native kernel init               |
| `make test_functional_utility` | Build functional utility test suite — 202 tests |
| `make test_friday_updates` | Build Friday Updates test suite — 135 tests        |
| `make test`            | Full CI pipeline — all 1841 tests                  |
| `make clean`           | Clean all build artifacts (compiler + seT6)        |
| `make all`             | Alias for `build-set6`                             |

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

seT6 headers are in `include/set6/` and the compiler's headers are in
`tools/compiler/include/`.  The top-level Makefile sets both:

```
-Iinclude -Itools/compiler/include
```

Key headers:

| Header                   | Purpose                                      |
|--------------------------|----------------------------------------------|
| `set6/trit.h`            | Core trit type, Kleene AND/OR/NOT, SIMD      |
| `set6/trit_type.h`       | Range-checked construction, fault flags      |
| `set6/trit_cast.h`       | Bool↔trit embed/project, int narrowing       |
| `set6/trit_emu.h`        | 2-bit packed encoding, bulk ops, registers   |
| `set6/memory.h`          | Tryte-aligned page allocator                 |
| `set6/ipc.h`             | Synchronous endpoints, async notifications   |
| `set6/scheduler.h`       | Trit-priority scheduling                     |
| `set6/syscall.h`         | Syscall dispatch ABI (14 syscalls)           |
| `set6/multiradix.h`      | DOT_TRIT, FFT_STEP, RADIX_CONV, load bal.   |
| `set6/wcet.h`            | WCET probe telemetry                         |
| `set6/qemu_trit.h`       | QEMU noise injection for testing             |
| `set6/sel4_ternary.h`    | Full seL4 kernel object model (THE MOONSHOT) |
| `set6/posix.h`           | POSIX compatibility / translation layer      |
| `set6/dev_trit.h`        | `/dev/trit` device driver ioctls             |
| `set6/tbe_shell.h`       | TBE shell command definitions                |
| `set6/ternary_weight_quantizer.h` | BitNet b1.58 weight quantization    |
| `set6/dlfet_sim.h`       | Samsung DLFET-RM gate simulator               |
| `set6/radix_transcode.h` | Binary↔ternary radix conversion               |
| `set6/srbc.h`            | Self-referential bias calibration              |
| `set6/trit_crypto.h`     | Quantum-resistant ternary cryptography         |
| `set6/prop_delay.h`      | Asymmetric propagation delay modeling          |
| `set6/ternary_temporal.h`| 3-valued temporal logic (LTL₃)                 |
| `set6/pam3_transcode.h`  | PAM-3/4 chip-to-chip interconnect              |
| `set6.h` (compiler)      | Legacy syscall ABI, capability structs       |

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
- [x] Unit tests for all kernel modules — **178 tests PASS** (`make set6_native`)
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

### Phase 6: Functional Utility Extension — DONE

**Goal:** Extend seT6 with 8 capability layers anticipating Samsung DLFET-RM,
quantum-resistant crypto, PAM-3/4 physical-layer interconnect, and
real-time verification — all without modifying the microkernel core.

- [x] **Ternary Weight Quantizer** — BitNet b1.58 quantization, ternary dot product, energy modeling
- [x] **DLFET-RM Gate Simulator** — Samsung/UNIST TNAND/TNOR/THA/TFA behavioral simulation
- [x] **Radix Transcode Engine** — Low-latency binary↔ternary conversion (Avizienis signed-digit)
- [x] **Self-Referential Bias Calibration** — Feedback loop with tamper detection, SNM tracking
- [x] **Ternary Cryptographic Hardening** — Sponge hash, cipher (mod-3 addition with inverse), LWE lattice
- [x] **Propagation Delay Modeling** — Asymmetric 6-transition delay with PVT adjustment
- [x] **Ternary Temporal Logic (LTL₃)** — 3-valued ALWAYS/EVENTUALLY/NEVER/UNTIL for safety analysis
- [x] **PAM-3/4 Transcode** — Chip-to-chip interconnect simulation, eye diagram, PAM-4 interop
- [x] **Verilog HW** — Ternary full adder (`hw/ternary_full_adder.v`), Wallace tree multiplier (`hw/ternary_wallace_tree.v`)
- [x] **Trit Linux driver registry** — Module driver framework with self-tests for all 11 modules
- [x] **Trithon bindings** — Python classes + C extension wrappers for all 8 modules
- [x] **202 functional utility tests** — 9 sections, cross-module integration verified
- [x] **1012+ total tests passing** across 35 suites

### Phase 7: Friday Updates — STT-MRAM, T-IPC, TFS — DONE

**Goal:** Add three ternary-native subsystem modules — STT-MRAM memory interface,
T-IPC compressed IPC protocol, and TFS file system — all out-of-band, without
modifying the seT6 microkernel core.

- [x] **STT-MRAM Memory Interface** — Biaxial MTJ ternary storage (3 resistance states), LiM command set, 5-trit→byte packing, ECS drift detection/recalibration
- [x] **Ternary-Native IPC (T-IPC)** — Balanced Ternary Huffman compression (0→1bit, ±1→2bits), Guardian Trit integrity checksum, Radix Integrity Guard, XOR differential updates
- [x] **Ternary-Native File System (TFS)** — Tryte-chain files (243-trit blocks), trit-tree directories, Huffman compression, POSIX extensions, 58% density gain over binary
- [x] **Verilog HW** — Sense amplifier (`hw/ternary_sense_amp.v`), T-IPC compressor (`hw/tipc_compressor.v`), TFS Huffman encoder (`hw/tfs_huffman.v`)
- [x] **Trit Linux awareness** — Feature flags (TRIT_FEAT_MRAM/TIPC/TFS), 3 new driver registrations with self-tests
- [x] **Trithon bindings** — C extension wrappers + Python classes for MRAM, T-IPC, TFS
- [x] **135 Friday Update tests** — 5 scenarios: STT-MRAM, T-IPC, TFS, cross-module integration, spec compliance
- [x] **1147+ total tests passing** across 36 suites

### Phase 8 — Arch-Inspired Enhancements (seT6-exclusive)

- [x] **LEGO-Like Modularity** (`trit_linux/modular/`) — Module registration, dependency DAG, drop-in key=value configs, Radix Integrity Guard (binary creep detection), load/unload lifecycle — 49 tests
- [x] **Secure Inter-Module Communication** (`trit_linux/ipc/`) — Ternary socket activation (on-demand like systemd), namespace isolation (user/net/ipc), capability-gated send/recv, injection attack detection (all-True / out-of-range payloads), Unknown-state pause tracking — 40 tests
- [x] **Time Synchronization Protocols** (`trit_linux/time/`) — NTP-like source management with stratum/quality, authenticated sync, skew detection with circular history, MRAM persistent timestamps, trit-priority event queue, replay attack detection — 42 tests
- [x] **Attack Surface Reduction & Hardening** (`trit_linux/hardening/`) — Kernel parameter emulation (kptr_restrict, dmesg_restrict, ASLR, stack protection), restrictive mount options (noexec/nodev/nosuid/readonly), ternary firewall (nftables-like rules with ACCEPT/LOG/DROP), SUID audit scanning, hardening score computation — 55 tests
- [x] **1645 total tests passing** across 29 suites — 100% pass rate

### Phase 9 — MEGA Patent Alignment & Sigma 9 Validation

- [x] **PVT Stability Engine** (`trit_linux/hw/trit_stabilize.h/.c`) — 27-point PVT corner sweep (3×3×3), thermal/flicker/shot noise injection, cosmic-ray SEU simulation, meta-stability detection, SRBC recovery integration, stability PPM and worst-SNM tracking
- [x] **TMVM Accelerator** (`trit_linux/ai/trit_tmvm.h/.c`) — Ternary Matrix-Vector Multiply with (3;2) balanced compressor, sparsity-aware dot product (zero-skip), 256×256 support, energy model (5 aJ ternary vs 42 aJ binary), 88% PDP gain
- [x] **ECS Digital Gauge-Block** (`trit_linux/hw/trit_ecs_gauge.h/.c`) — Self-calibrating runtime with 16 monitor channels, T-Audit fault logging (128-entry circular buffer), IRQ emergency recalibration, hesitation counter (Unknown-state persistence), health trit
- [x] **TCAM Network Search** (`trit_linux/net/trit_tcam_net.h/.c`) — Priority-ordered CAM matching (128 entries), exact + wildcard search via Unknown positions, trit Hamming distance, similarity search, sub-ns latency emulation (800ps), energy tracking (50 fJ/search)
- [x] **Sigma 9 Validation Suite** (`tests/test_sigma9.c`) — 197 tests across 8 sections: PVT stability, TMVM accelerator, ECS gauge-block, TCAM net search, radix integrity guard, side-channel resistance, epistemic K3 logic, Guardian Trit meta-test
- [x] **Bug fixes**: trit_pack(-1) sign-extension fix, TCAM exact-match classification, Radix Guard MIXED enforcement
- [x] **1841 total tests passing** across 30 suites — 100% pass rate

---

## Testing

### Master Test Command

A single command runs **every** test suite (compiler + kernel + Trithon + TernBench)
end-to-end, non-interactively, and logs the results with a timestamp:

```bash
./run_all_tests.sh
```

This will:

1. Build the Ternary-C-compiler and run all 25 compiler test suites
2. Build and run all 7 seT6 kernel test suites
3. Run the Trithon Python self-test
4. Run the TernBench benchmark
5. Print a pass/fail summary
6. Save the full log to `TEST_RESULTS/<yy-MM-dd-hh-mm-ss>_all_tests.txt`

**No manual confirmation or interaction required.** The exit code is `0` if all
suites pass, `1` if any fail.

### Running Individual Test Suites

```bash
# ---- seT6 Kernel Tests ----
make set6_native && ./set6_native              # 178 kernel boot/module tests
make test_integration && ./test_integration    # 56 cross-module integration tests
make test_sel4_ternary && ./test_sel4_ternary  # 142 seL4 moonshot tests
make test_memory_safety && ./test_memory_safety        # 28 memory safety tests
make test_scheduler_concurrency && ./test_scheduler_concurrency  # 27 scheduler tests
make test_tbe && ./test_tbe                    # 31 TBE shell tests
make test_trit_linux && ./test_trit_linux      # 98 Trit Linux arch tests

# ---- Hardware HAL Tests ----
make test_huawei_hal && ./test_huawei_hal      # 47 Huawei CN119652311A HAL tests
make test_samsung_nand && ./test_samsung_nand  # 60 Samsung US11170290B2 NAND tests
make test_samsung_modem && ./test_samsung_modem  # 61 Samsung CN105745888A modem tests

# ---- Functional Utility Tests ----
make test_functional_utility && ./test_functional_utility  # 202 tests (8 modules + integration)

# ---- Friday Updates Tests ----
make test_friday_updates && ./test_friday_updates  # 135 tests (STT-MRAM, T-IPC, TFS)

# ---- Arch-Inspired Enhancement Tests (seT6-exclusive) ----
make test_modular && ./test_modular              # 49 LEGO-like modularity tests
make test_ipc_secure && ./test_ipc_secure        # 40 secure inter-module comms tests
make test_time && ./test_time                    # 42 time sync protocol tests
make test_hardening && ./test_hardening          # 55 hardening & firewall tests

# ---- Compiler Tests (submodule) ----
cd tools/compiler && make clean && make test   # All 25 compiler test suites

# ---- Python / Benchmarks ----
make test-trithon                              # Trithon self-test
make ternbench                                 # TernBench benchmark
```

### Test Results Logging

Every run of `./run_all_tests.sh` creates a timestamped log file:

```
TEST_RESULTS/
└── 26-02-13-20-30-59_all_tests.txt   # yy-MM-dd-hh-mm-ss format
```

These logs capture the complete stdout/stderr of every test suite for
post-mortem analysis, CI archival, and regression tracking.

### Test Suites

| Suite                       | Tests | What It Covers                                      |
|-----------------------------|-------|-----------------------------------------------------|
| `set6_native`               | 178   | Kernel boot, memory, IPC, scheduler, caps, multiradix, WCET, noise |
| `test_integration`          | 56    | Cross-module: mem→IPC→cap→sched→multiradix→WCET     |
| `test_sel4_ternary`         | 142   | seL4 moonshot: all 11 kernel objects + POSIX layer   |
| `test_memory_safety`        | 28    | OOB, double-free, scrub-on-free, OOM, stats          |
| `test_scheduler_concurrency`| 27    | Priority scheduling, yield, block/unblock, capacity  |
| `test_tbe`                  | 31    | TBE env vars, consensus, accept_any, FFT, DOT, WCET |
| `test_trit_linux`           | 98    | Trit Linux: boot, pages, IRQ, timer, net, IPC        |
| `test_huawei_hal`           | 47    | Huawei CN119652311A ternary chip HAL                 |
| `test_samsung_nand`         | 60    | Samsung US11170290B2 NAND inference HAL              |
| `test_samsung_modem`        | 61    | Samsung CN105745888A ternary sequence modem           |
| `test_functional_utility`   | 202   | TWQ, DLFET, radix, SRBC, crypto, delay, TTL, PAM-3  |
| `test_friday_updates`       | 135   | STT-MRAM, T-IPC, TFS, cross-module, spec compliance |
| Compiler (25 suites)        | 250+  | Parser, codegen, VM, IR, linker, selfhost, hardware  |
| Trithon                     | —     | Python trit type, Kleene ops, C extension, 11 modules|
| TernBench                   | —     | Pi, dot product, radix, census, power benchmarks     |
| `test_modular`              | 49    | LEGO-like modularity, deps, configs, radix guard     |
| `test_ipc_secure`           | 40    | Ternary sockets, caps, namespaces, injection detect  |
| `test_time`                 | 42    | Time sources, sync, skew, MRAM, events, replay       |
| `test_hardening`            | 55    | Kernel params, mounts, firewall, SUID audit, score   |
| **Total**                   |**1645**| **All suites passing — 0 failures**                |

### Expected Master Test Output

```
$ ./run_all_tests.sh
...
========================================
  MASTER TEST SUMMARY
========================================
  Total suites : 34
  Passed       : 34
  Failed       : 0
========================================
  Log saved to: TEST_RESULTS/26-02-13-20-30-59_all_tests.txt
========================================
```

### Test Integrity Philosophy

seT6 follows the same verification philosophy as seL4: **every test must
prove something true about the system — never merely that code executes
without crashing.**

- **No tautological assertions.** Every `ASSERT` checks a computed value
  against an independently verifiable expected value. There are zero
  `ASSERT_TRUE(1)` placeholders in the test suite.
- **Mathematically grounded.** Ternary arithmetic tests verify against
  balanced-ternary truth tables: `1+1 = -1 carry 1`, `(-1)+(-1) = 1 carry -1`,
  `consensus(5,3) = -4`, `accept_any(5,3) = 12`.
- **Error paths tested.** Double-free returns `-1`. OOB writes rejected.
  Capability escalation blocked. Unknown syscalls return `-1`.
- **Boundary conditions verified.** True 9-trit max/min (`±9841`), overflow
  wrapping, OOM exhaustion, scheduler capacity limits.
- **Round-trip fidelity.** Every integer in the representable range survives
  `int → trit_word → int` conversion exactly.
- **No dead code.** Every test file compiles, links, runs, and is exercised
  by `./run_all_tests.sh`. There are no aspirational stubs referencing
  undefined APIs.

---

## TBE — Ternary Bootstrap Environment

The TBE is seT6's minimal userspace shell — the first program that
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
tbe> echo Hello from seT6
Hello from seT6
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
TBE: Shutting down seT6 kernel...
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
make set6_native && ./set6_native

# 4. Check for regressions (if tests fail)
git bisect start
git bisect bad HEAD
git bisect good <last-known-good-commit>
# Git bisect will binary-search for the breaking commit

# 5. Isabelle proofs (Phase 3+)
isabelle build -d proof/ -b seT6_Proofs
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
seT6/
├── ARCHITECTURE.md          # Full microkernel architecture (16 sections)
├── Makefile                 # Top-level build (14+ targets)
├── run_all_tests.sh         # Master test runner (34 suites)
├── README.md                # This file
├── LICENSE                  # GPL-2.0
├── TEST_RESULTS/            # Timestamped test logs (gitignored)
├── TODOLIST.md              # Development roadmap (all phases complete)
├── log.md                   # Development log
│
├── include/set6/            # seT6 core headers (24 headers)
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
│   ├── tbe_shell.h          #   TBE shell command definitions
│   ├── ternary_weight_quantizer.h  # BitNet b1.58 quantization
│   ├── dlfet_sim.h          #   Samsung DLFET-RM gate simulator
│   ├── radix_transcode.h    #   Binary↔ternary conversion
│   ├── srbc.h               #   Self-referential bias calibration
│   ├── trit_crypto.h        #   Ternary cryptographic primitives
│   ├── prop_delay.h         #   Propagation delay modeling
│   ├── ternary_temporal.h   #   3-valued temporal logic (LTL₃)
│   ├── pam3_transcode.h     #   PAM-3/4 interconnect transcode
│   ├── stt_mram.h           #   STT-MRAM Biaxial MTJ memory interface
│   ├── tipc.h               #   Ternary-Native IPC (Huffman + Guardian)
│   └── tfs.h                #   Ternary-Native File System
│
├── src/                     # Kernel source code
│   ├── init.c               #   Kernel bootstrap (178 tests)
│   ├── memory.c             #   Page allocator implementation
│   ├── ipc.c                #   IPC implementation
│   ├── scheduler.c          #   Scheduler implementation
│   ├── syscall.c            #   Syscall dispatch implementation
│   ├── multiradix.c         #   Multi-radix engine implementation
│   ├── tbe_main.c           #   TBE bootstrap shell (15 commands)
│   ├── ternary_weight_quantizer.c  # TWQ implementation
│   ├── dlfet_sim.c          #   DLFET gate behavioral sim
│   ├── radix_transcode.c    #   Radix conversion engine
│   ├── srbc.c               #   Bias calibration feedback loop
│   ├── trit_crypto.c        #   Hash, cipher, MAC, lattice
│   ├── prop_delay.c         #   Delay lookup + PVT adjustment
│   ├── ternary_temporal.c   #   LTL₃ operator evaluation
│   ├── pam3_transcode.c     #   PAM-3/4 encode/decode
│   ├── stt_mram.c           #   STT-MRAM memory interface implementation
│   ├── tipc.c               #   T-IPC Huffman compress/decompress, Guardian
│   └── tfs.c                #   TFS file ops, Huffman, trit-tree directories
│
├── tests/                   # Test suites
│   ├── test_integration.c   #   56 integration tests
│   ├── test_sel4_ternary.c  #   142 moonshot validation tests
│   ├── test_memory_safety.c #   28 memory safety tests
│   ├── test_scheduler_concurrency.c  # 27 scheduler tests
│   ├── test_tbe.c           #   31 TBE tests
│   ├── test_trit_linux.c    #   98 Trit Linux arch tests
│   ├── bench_unroll.c       #   SIMD unroll benchmark
│   ├── test_functional_utility.c  # 202 functional utility tests
│   └── test_friday_updates.c      # 135 Friday Updates tests (MRAM, T-IPC, TFS)
│
├── demo/                    # Demo programs
│   ├── trit_demo.c          #   Basic trit operations
│   ├── trit_type_demo.c     #   Type system demo
│   ├── trit_emu_bench.c     #   SIMD benchmark
│   └── clang_trit_demo.c    #   Multi-radix Clang demo
│
├── trithon/                 # Python Trithon interop
│   ├── trithon.py           #   Python trit type + Kleene ops + 11 module classes
│   └── trithon_ext.c        #   C extension: ctypes bridge to all modules
│
├── hw/                      # Ternary hardware modules (Verilog)
│   ├── ternary_full_adder.v #   DLFET-based NOT/NAND/HA/FA, ripple-carry adder
│   ├── ternary_wallace_tree.v # Wallace tree multiplier, MAC, dot product
│   ├── ternary_sense_amp.v  #   STT-MRAM sense amplifier, write driver, ECS
│   ├── tipc_compressor.v    #   T-IPC Huffman compressor/decompressor, Guardian
│   └── tfs_huffman.v        #   TFS Huffman encoder/decoder, sparse detector
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
    ├── include/             #   Compiler headers (set6.h syscall ABI)
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
# Verify seT6 headers exist
ls include/set6/trit*.h

# Verify compiler headers exist
ls tools/compiler/include/set6.h

# Check include flags in Makefile
grep -- "-I" Makefile
```

### Native build fails

```bash
# Manual compile with verbose output
gcc -Wall -Wextra -Iinclude -Itools/compiler/include -o set6_native src/init.c -v
```

### Regressions after changes

```bash
# Use git bisect to find breaking commit
git bisect start
git bisect bad HEAD
git bisect good <last-good-sha>
# Build + test at each step:
make clean && make set6_native && ./set6_native
git bisect good  # or: git bisect bad
```

---

## License & Future Plans

### License

seT6 is licensed under the **GNU General Public License v2.0** (GPL-2.0).
See [LICENSE](LICENSE) for the full text.

### Future Plans

- **Next:** Isabelle/HOL proofs for capability monotonicity (`CapSafety.thy`)
- **Next:** IPC correctness and memory isolation proofs
- **Hardware:** FPGA synthesis on iCE40 / Artix-7 using `hw/*.v` modules
- **Research:** CNTFET ternary gates for native ternary silicon
- **Long-term:** Huawei CFET / Samsung DLFET-RM / CMOS-ternary silicon targets
- **Crypto:** Post-quantum key exchange using ternary LWE lattice primitives
- **Interconnect:** PAM-3/4 physical layer validation on real SerDes hardware

### Contributing

See `tools/compiler/docs/CONTRIBUTING.md` for contribution guidelines.
All contributions must maintain the < 5% performance overhead gate and
pass the full test suite before merge.

---

*Built with balanced ternary logic — because two states were never enough.*


---

## Test Documentation Rule

> **MANDATORY**: All new tests MUST have a corresponding entry appended to
> [`TESTS_GLOSSARY_OF_ALL_TESTS.md`](TESTS_GLOSSARY_OF_ALL_TESTS.md) before
> the commit is considered complete. Each entry must include: suite assignment,
> line number, test description, section, assertion expression, and category.
> See the glossary for format details.
