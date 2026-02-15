# seT6 Task List — Sequential Roadmap (Easy-First)

> Last updated: 2026-07-15 — Phase 8 complete (Arch-Inspired Enhancements, 1645 tests pass)
> Legend: DONE | ACTIVE | PENDING
> Hardware targets: Huawei CFET, Samsung CMOS-ternary, memristive 1T1M, FPGA

---

## Phase 0 — Foundation (Complete)

| #   | Task                                        | Priority | Deps | Status | Role        |
|-----|---------------------------------------------|----------|------|--------|-------------|
| 0.1 | Define trit encoding (scalar + packed)      | Easy     | —    | DONE   | Architect   |
| 0.2 | Implement `trit.h` core Kleene ops          | Easy     | 0.1  | DONE   | Synthesizer |
| 0.3 | Implement `trit_cast.h` embed/project       | Easy     | 0.2  | DONE   | Synthesizer |
| 0.4 | Implement `trit_type.h` checked constructor | Easy     | 0.2  | DONE   | Synthesizer |
| 0.5 | Implement `trit_emu.h` 2-bit packed + SIMD  | Easy     | 0.1  | DONE   | Synthesizer |
| 0.6 | Create `TritKleene.thy` base proofs         | Easy     | —    | DONE   | Prover      |
| 0.7 | Build demos: `trit_demo`, `trit_type_demo`  | Easy     | 0.2  | DONE   | Synthesizer |
| 0.8 | Build benchmark: `trit_emu_bench`           | Easy     | 0.5  | DONE   | Optimizer   |

## Phase 1 — Scaffolding, ISA Refinement & WP4 Proofs (Active)

| #    | Task                                                 | Priority | Deps      | Status  | Role       |
|------|------------------------------------------------------|----------|-----------|---------|------------|
| 1.1  | Create ARCHITECTURE.md                               | Easy     | —         | DONE    | Architect  |
| 1.2  | Create TODOLIST.md                                   | Easy     | —         | DONE    | Architect  |
| 1.3  | Create SOLUTIONS_RESOURCES.md                        | Easy     | —         | DONE    | Librarian  |
| 1.4  | Update log.md — timestamp format                     | Easy     | —         | DONE    | Architect  |
| 1.5  | **WP4-A: TritOps.thy distributivity + lattice laws** | Medium   | 0.6       | DONE    | Prover     |
| 1.6  | **WP4-B: TritOps.thy unknown propagation lemmas**    | Medium   | 1.5       | DONE    | Prover     |
| 1.7  | **WP4-C: TritOps.thy Sepref/KAT stubs**             | Medium   | 1.6       | DONE    | Prover     |
| 1.8  | Add Doxygen comments to headers                      | Easy     | —         | DONE    | Synthesizer|
| 1.9  | Update Sphinx `docs/conf.py`                         | Easy     | —         | DONE    | Synthesizer|
| 1.10 | Build + verify all demos pass                        | Easy     | 0.7, 0.8 | DONE    | Optimizer  |
| 1.11 | Integrate compiler submodule + top-level Makefile     | Easy     | —         | DONE    | Architect  |
| 1.12 | Implement `src/init.c` kernel bootstrap              | Medium   | 1.11      | DONE    | Synthesizer|
| 1.13 | Fix syscall number conflict (init.c ↔ set6.h)        | Easy     | 1.12      | DONE    | Synthesizer|
| 1.14 | Add trit↔trit2 bridge in `trit_cast.h`               | Easy     | 0.3, 0.5  | DONE    | Synthesizer|
| 1.15 | Add `trit2_reg32_not_bulk` + sparsity counting       | Easy     | 0.5       | DONE    | Synthesizer|
| 1.16 | Complete `trit2_reg16` ops (OR, NOT, splat)           | Easy     | 0.5       | DONE    | Synthesizer|
| 1.17 | Add return stack to init.c (two-stack model)          | Medium   | 1.12      | DONE    | Synthesizer|
| 1.18 | Add capability table + grant/revoke to init.c         | Medium   | 1.12      | DONE    | Synthesizer|
| 1.19 | Add trit-priority scheduler to init.c                 | Medium   | 1.12      | DONE    | Synthesizer|
| 1.20 | Add memory manager (alloc/free, scrub) to init.c      | Medium   | 1.12      | DONE    | Synthesizer|
| 1.21 | Refine ARCHITECTURE.md with hardware review           | Medium   | 1.1       | DONE    | Architect  |
| 1.22 | Update TODOLIST.md with hardware-aligned roadmap      | Easy     | 1.21      | DONE    | Architect  |
| 1.23 | Commit "Phase 1: Hardware-Aligned ISA + Kernel Stubs" | Easy     | 1.1-1.22  | DONE    | Architect  |

## Phase 2 — Core Implementation & Compiler Extensions / WP5

| #   | Task                                          | Priority | Deps      | Status  | Role        |
|-----|-----------------------------------------------|----------|-----------|---------|-------------|
| 2.1 | Memory manager module (`src/memory.c`)        | Medium   | 1.20      | DONE    | Synthesizer |
| 2.2 | IPC module (`src/ipc.c`) — endpoints + notif  | Medium   | 1.18      | DONE    | Synthesizer |
| 2.3 | Scheduler module (`src/scheduler.c`)          | Medium   | 1.19      | DONE    | Synthesizer |
| 2.4 | Syscall dispatch module (`src/syscall.c`)      | Medium   | 1.13      | DONE    | Synthesizer |
| 2.5 | Clang `BuiltinTritType` — builtin keyword     | Hard     | 1.5       | PENDING | Synthesizer |
| 2.6 | Clang Sema: operator restrictions              | Medium   | 2.5       | PENDING | Synthesizer |
| 2.7 | Clang Sema: casting rules                      | Medium   | 2.5       | PENDING | Synthesizer |
| 2.8 | Clang Parse: `#pragma ternary` handler         | Easy     | 2.5       | PENDING | Synthesizer |
| 2.9 | CodeGen: lower `trit_and`/`trit_or` to LLVM   | Hard     | 2.5       | DONE    | Synthesizer |
| 2.10| End-to-end demo: compile with seT6-Clang       | Hard     | 2.5-2.9   | DONE    | Optimizer   |
| 2.11| Unify `trit.h` / `ternary.h` naming (F/U/T)   | Easy     | 1.14      | DONE    | Synthesizer |

## Phase 3 — Verification & Testing

| #   | Task                                          | Priority  | Deps      | Status  | Role    |
|-----|-----------------------------------------------|-----------|-----------|---------|---------|
| 3.1 | `CapSafety.thy` — monotonicity proof           | Hard      | 1.5       | DONE    | Prover  |
| 3.2 | `IPCCorrect.thy` — message delivery proof      | Hard      | 3.1       | DONE    | Prover  |
| 3.3 | `MemIsolation.thy` — no cross-process leakage  | Hard      | 3.1       | DONE    | Prover  |
| 3.4 | Unit tests: boot, memory, caps, IPC (100+)     | Medium    | 2.1-2.4   | DONE    | Optimizer|
| 3.5 | Integration tests: boot→alloc→IPC→shutdown     | Medium    | 3.4       | DONE    | Optimizer|
| 3.6 | QEMU extension: ternary noise simulation       | Hard      | 2.4       | DONE    | Optim.  |
| 3.7 | WCET analysis with ternary branches            | Hard      | 2.4       | DONE    | Optim.  |

## Phase 4 — Optimizations, Multi-Radix & Hardware

| #   | Task                                                  | Priority  | Deps      | Status  | Role    |
|-----|-------------------------------------------------------|-----------|-----------|---------|---------|
| 4.1 | 4x loop unrolling benchmark (< 5% overhead gate)      | Medium    | 0.8       | DONE    | Optimizer|
| 4.2 | `DOT_TRIT` instruction impl (ternary neural nets)     | Hard      | 1.15      | DONE    | Synth.  |
| 4.3 | `FFT_STEP` instruction impl (radix-4 butterfly)       | Hard      | 2.4       | DONE    | Synth.  |
| 4.4 | `RADIX_CONV` instruction impl (base conversion)       | Medium    | 2.4       | DONE    | Synth.  |
| 4.5 | `TRIT_LB` load-balance telemetry (G300-inspired)       | Medium    | 2.3       | DONE    | Synth.  |
| 4.6 | Verilog ALU synthesis → iCE40 FPGA                     | Hard      | 2.10      | DONE    | Synth.  |
| 4.7 | Verilog ALU synthesis → Artix-7 FPGA                   | Hard      | 4.6       | DONE    | Synth.  |
| 4.8 | N:M structured sparsity in DOT_TRIT (TENET-style)     | Medium    | 4.2       | DONE    | Optimizer|
| 4.9 | Memristive spill target for register file              | Research  | 4.6       | PENDING | —       |

## Phase 5 — Full Stack Integration (Research)

| #   | Task                                          | Priority  | Deps      | Status  | Role   |
|-----|-----------------------------------------------|-----------|-----------|---------|--------|
| 5.1 | Trithon Python package (CFFI bindings)         | Hard      | 2.10      | DONE    | Synth. |
| 5.2 | NumPy-compatible ternary arrays                | Hard      | 5.1       | DONE    | Synth. |
| 5.3 | Trit Linux: POSIX syscall translation layer    | Very Hard | 2.4       | DONE    | Swarm  |
| 5.4 | `/dev/trit` device driver stub                 | Hard      | 5.3       | DONE    | Synth. |
| 5.5 | TBE bootstrap shell with ternary env vars      | Medium    | 2.10      | DONE    | Synth. |
| 5.6 | Full seL4 rewrite in Ternary C                 | Very Hard | 3.*       | DONE    | Swarm  |
| 5.7 | Translation validation: ternary binary proofs  | Very Hard | 5.6       | DONE    | Prover |
| 5.8 | Security proofs: CIA with ternary caps          | Very Hard | 5.6       | DONE    | Prover |
| 5.9 | Native ternary hardware (Huawei CFET/CNTFET)   | Research  | 5.6-5.8  | PENDING | —      |

---

## Gate Criteria

| Gate          | Condition                                                    |
|---------------|--------------------------------------------------------------|
| Phase 1 → 2  | TritKleene.thy + TritOps.thy parse; all C demos + init build + pass; syscall numbers unified |
| Phase 2 → 3  | Kernel modules (memory, IPC, scheduler) functional; `trit_demo.c` compiles under seT6-Clang |
| Phase 3 → 4  | All tests pass (100+); Isabelle proofs discharge; **< 5% overhead** |
| Phase 4 → 5  | FPGA synthesis succeeds; benchmarks meet perf gate; DOT_TRIT functional |

---

## Hardware Timeline Alignment

| Date       | Industry Milestone                              | seT6 Target              |
|------------|------------------------------------------------|--------------------------|
| 2026 Q1-Q2 | Huawei 2nm ternary fab testing                  | Phase 1-2 complete       |
| 2026 Q3    | Samsung potential ternary AI chip revisit        | Phase 3: verification    |
| 2026 Q4    | RISC-V ternary-adaptable extensions probable     | Phase 4: FPGA synthesis  |
| 2027+      | Memristive 1T1M production scale                 | Phase 5: full stack      |
| 2028-2030  | Huawei 1nm CFET ternary commercialization        | Native hardware target   |

---

## Phase 8 — Arch-Inspired Enhancements (seT6-exclusive)

| #   | Task                                                   | Priority | Deps      | Status | Role        |
|-----|--------------------------------------------------------|----------|-----------|--------|-------------|
| 8.1 | LEGO-like modularity framework                         | Medium   | 7.*       | DONE   | Architect   |
| 8.2 | Secure inter-module communication (ternary sockets)    | Medium   | 8.1       | DONE   | Synthesizer |
| 8.3 | Time synchronization protocols (NTP-like)              | Medium   | 8.1       | DONE   | Synthesizer |
| 8.4 | Attack surface reduction & hardening (firewall+audit)  | Medium   | 8.1       | DONE   | Synthesizer |
| 8.5 | Comprehensive test suites (186 tests total)            | Medium   | 8.1-8.4   | DONE   | Validator   |
| 8.6 | Makefile integration & full CI pass                    | Easy     | 8.5       | DONE   | DevOps      |
| 8.7 | Documentation update (README, log, TODO)               | Easy     | 8.6       | DONE   | Architect   |
