---
title: "Ternary World Roadmap"
date: 2026-02-17
last_updated: 2026-02-17
schema: "PARA — Resources/Areas"
purpose: "High-level model of the ternary computing ecosystem, updated from daily searches"
max_lines: 300
---

# Ternary World Roadmap

> Living document. Updated from daily search logs. Sections: Hardware, Software,
> Protocols, Patents/Papers. Summarize when > 300 lines.

---

## 1. Hardware

### 1.1 Transistor Technologies
| Technology | Vendor/Source | Status | seT6 Integration |
|------------|--------------|--------|-------------------|
| CFET (Complementary FET) ternary | Huawei CN119652311A | Patent granted 2025 | ✅ `hw/huawei_cn119652311a_alu.v`, `src/huawei_alu.c` |
| DLFET-RM (Dual-Level FET) | Samsung research | Published 2024 | ✅ `src/dlfet_sim.c`, `hw/ternary_full_adder.v` |
| TMD (Transition Metal Dichalcogenide) | TSMC research | Experimental | ✅ `hw/tsmc_tmd_fet.v`, `src/tsmc_tmd.c` |
| Carbon Nanotube Ternary Gates | Chinese Academy of Sciences | Research 2024–2025 | 📋 Tracked in CHINA_CARBON_NONBINARY_AI_CHIPS_RESEARCH.md |
| RRAM/Memristive Ternary | Multiple (Crossbar, Weebit) | Emerging 2025–2026 | ❌ Not yet integrated — TODO T-024 |

### 1.2 Memory Technologies
| Technology | Vendor/Source | Status | seT6 Integration |
|------------|--------------|--------|-------------------|
| STT-MRAM Biaxial MTJ | Various | Production 2024 | ✅ `src/stt_mram.c`, `hw/ternary_sense_amp.v` |
| NAND Flash Ternary Inference | Samsung US11170290B2 | Patent granted | ✅ `src/samsung_tbn.c` |
| TCAM Crossbar | SK Hynix | Production | ✅ `hw/hynix_tcam_crossbar.v`, `src/hynix_tcam.c` |
| PCM (Phase Change) Ternary | Intel/Micron | Research | ❌ Not yet tracked |

### 1.3 Interconnect
| Technology | Vendor/Source | Status | seT6 Integration |
|------------|--------------|--------|-------------------|
| PAM-3 SerDes | Intel | Production (Ethernet) | ✅ `src/intel_pam3_decoder.c`, `hw/intel_pam3_decoder.v` |
| PAM-4 Chip-to-Chip | Industry standard | Production | ✅ `src/pam3_transcode.c` (includes PAM-4 mode) |

---

## 2. Software

### 2.1 Operating Systems / Kernels
| Project | Description | Relation to seT6 |
|---------|-------------|-------------------|
| seT5/seT6 | Balanced ternary microkernel (this project) | Core |
| Trit Linux | Ternary Linux arch port (simulation) | ✅ `trit_linux/` — 6 subsystems, 252 tests |
| TBE | Ternary Bootstrap Environment | ✅ `src/tbe_main.c` — 31 tests |

### 2.2 Compilers / Toolchains
| Project | Description | Status |
|---------|-------------|--------|
| Ternary-C-compiler | Custom ternary C compiler (parser → codegen → VM → linker) | ✅ `tools/compiler/` — 149 tests |
| Clang trit extensions | `__trit` keyword, `#pragma ternary` | Stubs in `clang/` — NOT integrated into real LLVM |
| Trithon | Python ternary interop via C extension | ✅ `trithon/` — 99 tests |

### 2.3 Formal Verification Tooling
| Tool | Version | Description | Status |
|------|---------|-------------|--------|
| Isabelle/HOL | 2025-2 | Theorem prover for ternary proof theories | ✅ Installed at `/opt/isabelle/Isabelle2025-2/` |
| `tools/isabelle` | wrapper | Repo wrapper script (hardcoded path) | ✅ `tools/isabelle build -d proof seT6_Proofs` |
| `proof/*.thy` | 8 theories | TritKleene, TritOps, CapSafety, MemIsolation, IPCCorrect, SecurityCIA, TranslationValidation, TJSON_Validation | ✅ All proven |
| TESTS_AND_PROOFS_INSTRUCTIONS.md | — | Comprehensive proof/test development guide | ✅ Created |

### 2.4 Cryptography
| Primitive | Description | Status |
|-----------|-------------|--------|
| Ternary Sponge Hash | Mod-3 sponge construction | ✅ `src/trit_crypto.c` |
| Ternary LWE Lattice | Post-quantum lattice crypto | ✅ `src/trit_crypto.c` |
| Ternary Block Cipher | Mod-3 SPN cipher | ✅ `src/trit_crypto.c` |

---

## 3. Protocols

### 3.1 Communication
| Protocol | Description | Status |
|----------|-------------|--------|
| T-IPC | Ternary IPC with Huffman compression + Guardian Trit | ✅ `src/tipc.c` |
| T-Net | Ternary networking stack (MAC/IP/Transport) | ✅ `trit_linux/net/trit_net.c` |
| PAM-3 Physical Layer | Ternary signaling on copper/fiber | ✅ Emulated in `src/pam3_transcode.c` |

### 3.2 Storage
| Protocol | Description | Status |
|----------|-------------|--------|
| TFS | Ternary File System (tryte-chain, trit-tree dirs) | ✅ `src/tfs.c` |
| Ternary Database | CAM-based ternary key-value store | ✅ `src/ternary_database.c` (needs expansion) |

### 3.3 Standards Gaps
- No IETF/IEEE ternary encoding standard exists yet
- No formal wire protocol spec for trit-over-PAM-3 (TODO T-023)
- No ternary TLS/DTLS handshake spec

### 3.4 Ternary-First Bridge Protocol
> **Mandatory (effective 2026-02-20):** All interoperability between seT6's
> ternary internals and binary/non-ternary systems is achieved through
> **outward-facing bridge modules** at the system boundary. No internal
> binary regression is permitted. The conversion direction is always:
>
>     seT6 ternary core  ──▶  bridge/converter  ──▶  binary world
>
> Examples: `pam3_transcode.c` (PAM-3↔PAM-4), `trit_linux/` (POSIX↔trit),
> `trithon/` (Python↔trit). See `ARCHITECTURE.md` §14A for details.

---

## 4. Patents & Papers

### 4.1 Integrated Patents (7)
| Patent | Vendor | Year | Core Innovation |
|--------|--------|------|-----------------|
| CN119652311A | Huawei | 2025 | Balanced ternary CFET AI chip |
| US11170290B2 | Samsung | 2021 | NAND flash ternary inference |
| CN105745888A | Samsung | 2016 | Ternary sequence modulation |
| WO2016199157A1 | Ingole | 2016 | Ternary ALU (TALU) — all logic gates |
| (TSMC TMD) | TSMC | 2024 | TMD FET for multi-valued logic |
| (Intel PAM3) | Intel | 2023 | PAM-3 decoder for SerDes interconnect |
| (Hynix TCAM) | SK Hynix | 2023 | TCAM crossbar ternary content-addressable memory |

### 4.2 Tracked But Not Integrated
| Source | Topic | Value Score | Status |
|--------|-------|-------------|--------|
| Chinese Academy of Sciences | Carbon nanotube ternary gates | 8 | Documented, not integrated |
| Various RRAM vendors | Memristive ternary storage | 7 | Research-stage |

### 4.3 Search Targets
- RRAM/ReRAM ternary computing patents (2024–2026)
- Memristive crossbar ternary logic (HP Labs, Crossbar Inc.)
- Ternary neuromorphic chips (Intel Loihi successors)
- Multi-valued logic EDA tools patents
- Ternary quantum error correction codes

---

## 5. Market Signals

| Signal | Source | Implication | Date |
|--------|--------|-------------|------|
| PAM-3 adoption in 200G/400G Ethernet | IEEE 802.3 | Ternary signaling is production reality | 2024 |
| Samsung NAND 3-state inference | Samsung patent | Storage-compute convergence | 2021 |
| Huawei balanced ternary AI chip | Patent CN119652311A | Nation-state investment in ternary | 2025 |
| TSMC TMD research | TSMC labs | Sub-3nm may favor multi-valued logic | 2024 |
| Carbon nanotube ternary (China) | CAS publications | Government-backed ternary hardware R&D | 2025 |

---

*Last updated: 2026-02-17 — Next update: after daily search cycle*
