# seT6 Changelog

All notable changes to this project are documented in this file.
Format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [Unreleased]

### Added
- T-006: GitHub Actions CI pipeline (`make test` on push/PR, artifact upload)
- T-007: AddressSanitizer build target (`make test-asan`)
- T-008: Code coverage target (`make coverage` with gcov/lcov)
- T-009: Kernel fuzz testing harness (`make fuzz` with libFuzzer)
- T-010: Dockerfile for reproducible builds
- T-011: Verilog compile check (`make verilog-check` with iverilog)
- T-012: DTS validation (`make dts-check` with dtc)
- T-014/T-035: `proof/TernaryArith.thy` — balanced ternary adder correctness
- T-016: `src/time_sync_daemon.c` — NTP-like ternary time synchronization
- T-017: `src/namespace_isolation.c` — process namespace isolation
- T-018: `src/audit_firewall.c` — ternary audit log + firewall
- T-019: Performance benchmark target (`make bench`)
- T-021: Doxygen documentation target (`make docs`)
- T-022: This CHANGELOG.md
- T-023: Ternary network protocol specification
- T-036: `proof/TCAMSearch.thy` — TCAM 3-value match correctness
- T-037: `proof/LatticeCrypto.thy` — LWE ternary hardness in GF(3)
- T-038: `proof/HuffmanTernary.thy` — base-3 Huffman optimality
- T-039: `proof/SIMDPacked.thy` — packed64 trit SIMD correctness
- T-040: PAM-3 IEEE 802.3 bridge specification
- T-042: `src/ternary_snn.c` — ternary spiking neural network
- T-045–T-049: Gödel machine core modules
- T-050–T-053: Gödel machine formal verification proofs
- T-054–T-058: Gödel machine infrastructure

## [Phase 8] — 2026-02-17

### Added
- Crown Jewel Reversion Guard test suite (T-025): 45 KAT vectors
- `test_ternary_database.c` expanded: 32 tests covering CRUD, CAM, RLE, Huffman, NULL propagation
- `test_ai_acceleration.c`: 24 tests for BitNet, DLFET, sparse NN
- `test_fault_tolerant_network.c`: 25 tests for Hamming ECC, routing, consensus
- `test_adversarial.c`: 34 negative-path tests
- README updated: 1792+ tests across 34 suites

## [Phase 7] — 2026-01-13

### Added
- STT-MRAM memory interface (`src/stt_mram.c`, `include/set5/stt_mram.h`)
- T-IPC compressed IPC (`src/tipc.c`, `include/set5/tipc.h`)
- TFS ternary file system (`src/tfs.c`, `include/set5/tfs.h`)
- Verilog: sense amplifier, T-IPC compressor, TFS Huffman encoder
- 135 Friday Update tests — 1147+ total passing

## [Phase 6] — 2025-12-20

### Added
- 8 functional utility modules: TWQ, DLFET, Radix, SRBC, Crypto, Delay, Temporal, PAM-3
- Verilog: full adder, Wallace tree multiplier
- Trit Linux driver registry with 11 module self-tests
- 202 functional utility tests — 1012+ total passing

## [Phase 5] — 2025-11-15

### Added
- seL4 moonshot: full kernel object model (1170 lines, 11 object types, 142 tests)
- TBE bootstrap shell (15 commands, env vars, Trithon hook)
- Trithon Python interop layer
- 407 total tests passing

## [Phase 4] — 2025-10-01

### Added
- Multi-radix engine: DOT_TRIT, FFT_STEP, RADIX_CONV
- 4x loop unrolling (< 5% overhead gate met)
- Verilog ALU + FPGA constraints (iCE40, Artix-7)
- QEMU noise injection + WCET telemetry

## [Phase 3] — 2025-08-15

### Added
- 178 kernel unit tests, 56 integration tests
- Isabelle: TritKleene.thy, TritOps.thy proofs

## [Phase 2] — 2025-07-01

### Added
- Memory manager, IPC, scheduler, syscall dispatch
- Kernel boot with 178 tests passing

## [Phase 1] — 2025-05-15

### Added
- ARCHITECTURE.md, TODOLIST.md, SOLUTIONS_RESOURCES.md
- Core headers: trit.h, trit_type.h, trit_cast.h, trit_emu.h
- Compiler submodule integration
- Kernel bootstrap (src/init.c)

## [Phase 0] — 2025-04-01

### Added
- Initial trit encoding and Kleene operators
- Demo programs
- TritKleene.thy formal proof
