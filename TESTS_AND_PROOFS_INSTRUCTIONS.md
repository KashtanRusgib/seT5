---
title: "seT6 Tests & Formal Proofs — Complete Instructions"
date: 2026-02-17
last_updated: 2026-02-18
schema: "SOP — Standard Operating Procedure"
purpose: "Master reference for running all tests and Isabelle/HOL proofs in seT6"
maintainer: "AI Flywheel + Human Review"
isabelle_version: "Isabelle2025-2"
total_tests: 5280
total_suites: 66
total_proofs: 8
proof_session: "seT6_Proofs"
---

# seT6 Tests & Formal Proofs — Complete Instructions

> **This document is the single source of truth for running, verifying, and
> extending the seT6 test suites and Isabelle/HOL formal proofs.**
> It is updated every time new tests or proofs are added.

> **⚠️ TEST GLOSSARY PROTOCOL**: Every new test MUST be logged in
> [`seT6/TESTS_GLOSSARY_OF_ALL_TESTS.md`](seT6/TESTS_GLOSSARY_OF_ALL_TESTS.md)
> before a commit is considered valid. The glossary tracks 5280+ runtime
> assertions across 66 active test suites (69 total including 3 disabled).
> See the glossary's "Rule: Future Test Documentation" section for the full
> 4-step checklist: (1) glossary entry → (2) Makefile registration →
> (3) run_all_tests.sh update → (4) `make alltest` verification.

---

## Table of Contents

1. [Quick Start](#1-quick-start)
2. [Prerequisites](#2-prerequisites)
3. [Running All Tests](#3-running-all-tests)
4. [Test Suite Catalog](#4-test-suite-catalog)
5. [Isabelle/HOL Installation](#5-isabellehol-installation)
6. [Running Formal Proofs](#6-running-formal-proofs)
7. [Proof Catalog](#7-proof-catalog)
8. [Adding New Tests](#8-adding-new-tests)
9. [Adding New Proofs](#9-adding-new-proofs)
10. [Troubleshooting](#10-troubleshooting)
11. [Quality Standard](#11-quality-standard)

---

## 1. Quick Start

```bash
# Run all 1792 tests across 34 suites (expected: 0 failures)
make test6

# Run Isabelle proofs (requires Isabelle2025-2 installed)
tools/isabelle build -d proof seT6_Proofs

# Run a specific test suite only
make test-adversarial          # via seT6/Makefile
make test-ai-acceleration      # via seT6/Makefile
make test-ft-network           # via seT6/Makefile
```

---

## 2. Prerequisites

### For Tests (C compilation)

| Tool      | Minimum Version | Check Command         |
|-----------|-----------------|-----------------------|
| GCC       | 11+             | `gcc --version`       |
| GNU Make  | 4.3+            | `make --version`      |
| Bash      | 5.0+            | `bash --version`      |

All test suites compile from C source with `gcc -std=c11`. No external
libraries are required — every dependency is self-contained in `src/` and
`include/set5/`.

### For Formal Proofs (Isabelle/HOL)

| Tool              | Required Version | Check Command               |
|-------------------|------------------|-----------------------------|
| Isabelle/HOL      | 2025-2           | `tools/isabelle version`    |
| Disk space        | ~2 GB            | For Isabelle + HOL image    |
| RAM               | 4+ GB            | For proof checking          |

---

## 3. Running All Tests

### Full Suite (Recommended)

```bash
make test6
```

This command:
1. Compiles all test binaries from `tests/` and integration test directories
2. Runs each suite sequentially, collecting pass/fail counts
3. Invokes `tools/test_grand_summary.sh` to produce a unified report
4. Prints the grand summary: total tests, total suites, pass rate

**Expected output (current baseline):**

```
╔══════════════════════════════════════════════════════════════╗
║         seT5 GRAND TEST SUMMARY — ALL SUITES               ║
╚══════════════════════════════════════════════════════════════╝
  Total tests : 1792
  Passed      : 1792
  Failed      : 0
  Suites      : 34 / 34
  Result      : *** ALL 1792 TESTS PASSED — SIGMA 9 ***
```

### Individual Suites

From the root Makefile, suites run as part of `_run-test-suites`. To run
individual suites, use the seT6/Makefile targets:

```bash
cd seT6 && make test-ai-acceleration
cd seT6 && make test-ft-network
cd seT6 && make test-adversarial
cd seT6 && make test-ternary-database
```

Or compile and run a single test binary directly:

```bash
gcc -std=c11 -Iinclude -o /tmp/test_adversarial tests/test_adversarial.c
/tmp/test_adversarial
```

### Test Log Files

Every `make test6` run saves a timestamped log to `TEST_RESULTS/`:

```
TEST_RESULTS/test_run_2026-02-17_143022.log
```

---

## 4. Test Suite Catalog

### 4.1 Core Kernel Suites (seT5 Heritage)

| # | Suite Name | Source File(s) | Tests | What It Verifies |
|---|-----------|----------------|-------|------------------|
| 1 | seT5 Boot (Native) | `set5_native` | 14 | Native boot sequence, trit register init |
| 2 | Integration | `test_integration/` | 89 | Cross-module integration (cap+mem+IPC+scheduler) |
| 3 | seL4 Ternary | `test_sel4_ternary/` | 52 | seL4 ternary extensions (Kleene logic, cap model) |
| 4 | Memory Safety | `test_memory_safety/` | 58 | Memory alloc/free, scrub-on-free, page isolation |
| 5 | Scheduler & Concurrency | `test_scheduler_concurrency/` | 34 | Thread scheduling, priority, quantum management |
| 6 | TBE Bootstrap | `test_tbe/` | 31 | Ternary Bootstrap Environment startup |

### 4.2 Patent Integration Suites

| # | Suite Name | Source File(s) | Tests | Patent |
|---|-----------|----------------|-------|--------|
| 7 | Huawei CN119652311A | `test_huawei_cn119652311a/` | 48 | Balanced ternary CFET ALU |
| 8 | Samsung US11170290B2 | `test_samsung_us11170290b2/` | 47 | NAND flash ternary inference |
| 9 | Samsung CN105745888A | `test_samsung_cn105745888a/` | 36 | Ternary sequence modem |
| 10 | TSMC/Intel/Hynix | `test_tsmc_tmd_intel_pam3_hynix_tcam/` | 81 | TMD FET, PAM-3, TCAM |
| 11 | Ingole WO2016199157A1 | `tests/test_ingole_talu.c` | 32 | TALU — all ternary logic gates |

### 4.3 Feature Extension Suites

| # | Suite Name | Source File(s) | Tests | What It Verifies |
|---|-----------|----------------|-------|------------------|
| 12 | Ternary Database | `tests/test_ternary_database.c` | 32 | CRUD, CAM, RLE, Huffman, NULL propagation |
| 13 | AI Acceleration | `tests/test_ai_acceleration.c` | 24 | BitNet quantize/forward, DLFET, sparse NN |
| 14 | Fault-Tolerant Network | `tests/test_fault_tolerant_network.c` | 25 | Hamming ECC (81 patterns), routing, consensus |
| 15 | Adversarial | `tests/test_adversarial.c` | 34 | OOB, double-free, UAF, revoked caps, fuzzing |

### 4.4 Functional & Update Suites

| # | Suite Name | Source File(s) | Tests | What It Verifies |
|---|-----------|----------------|-------|------------------|
| 16 | Functional Utility | `test_functional_utility/` | 92 | 8 capability layers from INCREASE_FUNCTIONAL_UTILITY |
| 17 | Friday Updates | `test_friday_updates/` | 111 | STT-MRAM, T-IPC, TFS |

### 4.5 Compiler Suite (7 Sub-Suites)

| # | Suite Name | Tests | What It Verifies |
|---|-----------|-------|------------------|
| 18 | Lexer | 17 | Token scanning |
| 19 | Parser | 17 | AST construction |
| 20 | Semantic | 17 | Type checking, scope |
| 21 | Codegen | 17 | Bytecode generation |
| 22 | VM | 24 | Virtual machine execution |
| 23 | Linker | 21 | Module linking |
| 24 | End-to-End | 36 | Full pipeline (source → execute) |

Source: `tools/compiler/tests/`

### 4.6 Trithon Suite

| # | Suite Name | Source File(s) | Tests | What It Verifies |
|---|-----------|----------------|-------|------------------|
| 25 | Trithon Self-Test | `trithon/trithon_test.c` | 99 | Python-ternary interop, C extension |

### 4.7 Trit Linux Suites (9 Sub-Suites)

| # | Suite Name | Tests | What It Verifies |
|---|-----------|-------|------------------|
| 26 | Trit Linux Arch | 252 | Base ternary Linux architecture |
| 27 | Enhancement: KConfig | varies | Kernel configuration ternary extensions |
| 28 | Enhancement: SecureBoot | varies | Ternary secure boot chain |
| 29 | Enhancement: Audit | varies | Ternary audit subsystem |
| 30 | Enhancement: SELinux | varies | Ternary SELinux policies |
| 31 | Enhancement: Netfilter | varies | Ternary packet filtering |
| 32 | Enhancement: Cgroups | varies | Ternary cgroup management |

Source: `trit_linux/`, `test_trit_linux/`, `test_trit_enhancements/`

### 4.8 seT6-Specific Suites

| # | Suite Name | Source File(s) | Tests | What It Verifies |
|---|-----------|----------------|-------|------------------|
| 33 | seT6 Extensions | `seT6/tests/` | varies | seT6-specific kernel extensions |
| 34 | Ternary Database (seT6) | `seT6/tests/test_ternary_database.c` | 4+ | seT6 database layer |

**Grand Total: 1792 tests across 34 suites — 100% pass rate required (Sigma 9)**

---

## 5. Isabelle/HOL Installation

### Current Installation

Isabelle2025-2 is installed at `/opt/isabelle/Isabelle2025-2` (outside the
git repository to avoid tracking ~2 GB of binaries). A convenience symlink
and wrapper are provided:

| Artifact | Path | Purpose |
|----------|------|---------|
| Installation | `/opt/isabelle/Isabelle2025-2/` | Full Isabelle2025-2 distribution |
| Symlink | `Isabelle2025-2/` (repo root) | Local access (gitignored) |
| Wrapper | `tools/isabelle` | Executable script, hardcodes correct path |

### Fresh Installation (New Developer Setup)

If Isabelle is not yet installed on your system:

```bash
# 1. Download Isabelle2025-2 for Linux (~1.2 GB)
curl -L -o /tmp/Isabelle2025-2_linux.tar.gz \
  "https://isabelle.in.tum.de/dist/Isabelle2025-2_linux.tar.gz"

# 2. Extract to /opt/isabelle (requires sudo)
sudo mkdir -p /opt/isabelle
sudo tar -xzf /tmp/Isabelle2025-2_linux.tar.gz -C /opt/isabelle

# 3. Create repo symlink (already gitignored)
ln -sfn /opt/isabelle/Isabelle2025-2 Isabelle2025-2

# 4. Verify installation
tools/isabelle version
# Expected output: Isabelle2025-2

# 5. Clean up tarball
rm /tmp/Isabelle2025-2_linux.tar.gz
```

### Docker Alternative

```bash
docker run --rm -v "$PWD":/work -w /work \
  makarius/isabelle:Isabelle2025-2 \
  isabelle build -d proof seT6_Proofs
```

### Important Notes

- The `tools/isabelle` wrapper **hardcodes** the path `/opt/isabelle/Isabelle2025-2`
  to avoid conflicts with any other Isabelle installations on the system PATH.
- The `Isabelle2025-2/` symlink at repo root is in `.gitignore` (line 87).
- If you have a different Isabelle version installed system-wide, always use
  `tools/isabelle` (not bare `isabelle`) to ensure the correct version.

---

## 6. Running Formal Proofs

### Build All Proofs

```bash
# Build the complete proof session (all 8 theories)
tools/isabelle build -d proof seT6_Proofs
```

This command:
1. Loads HOL (Higher-Order Logic) as the base session
2. Processes all 8 theory files in dependency order
3. Type-checks every definition, verifies every lemma and theorem
4. Reports success/failure for each theory

**Expected output:** All 8 theories checked successfully with 0 errors.

### Build with Verbose Output

```bash
tools/isabelle build -v -d proof seT6_Proofs
```

### Check a Single Theory (Interactive)

```bash
# Open Isabelle/jEdit IDE with a specific theory
tools/isabelle jedit -d proof -l HOL proof/TritKleene.thy
```

### Proof Session Definition

The session is defined in [proof/ROOT](proof/ROOT):

```
session seT6_Proofs = HOL +
  description "seT6 Ternary Microkernel — Formal Verification Proofs"
  theories
    TritKleene
    TritOps
    CapSafety
    MemIsolation
    IPCCorrect
    SecurityCIA
    TranslationValidation
    TJSON_Validation
```

**Base session:** `HOL` (Higher-Order Logic from Isabelle's standard library).
All 8 theories are checked in the order listed.

---

## 7. Proof Catalog

### Dependency Graph

```
HOL (Isabelle standard library)
 └── TritKleene.thy        ← Defines trit datatype + Kleene K₃ algebra
      └── TritOps.thy      ← Extends with distributivity, identity, monotonicity
           ├── CapSafety.thy       ← Capability grant/revoke safety
           ├── MemIsolation.thy    ← Memory page isolation guarantees
           └── IPCCorrect.thy      ← IPC message integrity + state machine
 └── SecurityCIA.thy       ← CIA triad (standalone trit definition)
 └── TranslationValidation.thy  ← Compiler correctness (standalone trit)
 └── TJSON_Validation.thy  ← Ternary JSON validation (imports TritKleene + TritOps)
```

### Theory Descriptions

#### 1. TritKleene.thy — Kleene Three-Valued Logic Foundation

| Property | Value |
|----------|-------|
| File | [proof/TritKleene.thy](proof/TritKleene.thy) |
| Imports | `Main` (Isabelle/HOL) |
| Lines | ~82 |
| Key definitions | `trit` datatype (`Neg \| Unk \| Pos`), `trit_and` (min), `trit_or` (max), `trit_not` |
| Key theorems | Commutativity, associativity, involution, De Morgan (AND/OR), unknown absorption, binary collapse |
| C correspondence | `include/set5/trit.h` — `trit_and()`, `trit_or()`, `trit_not()` |

**What it proves:** The `trit` datatype forms a bounded distributive lattice
under Kleene's strong K₃ logic. `Neg < Unk < Pos` is a total order.
NOT is an involution. De Morgan's laws hold. The Unknown state absorbs in
both AND and OR (the defining property separating K₃ from classical logic).
When restricted to `{Neg, Pos}`, Kleene logic collapses to classical Boolean
logic.

#### 2. TritOps.thy — Extended Ternary Operator Properties

| Property | Value |
|----------|-------|
| File | [proof/TritOps.thy](proof/TritOps.thy) |
| Imports | `TritKleene` |
| Lines | ~215 |
| Key definitions | (inherits from TritKleene) |
| Key theorems | OR associativity, AND/OR distributivity, identity elements, annihilators, idempotence, absorption, unknown propagation, monotonicity |
| C correspondence | All trit arithmetic in `src/` uses these properties |

**What it proves:** Complete algebraic characterization of the K₃ lattice:
Pos is AND-identity and OR-annihilator; Neg is AND-annihilator and
OR-identity. Both operators are idempotent. Absorption laws hold.
Unknown propagates unless paired with Neg (for AND) or Pos (for OR).
AND and OR are monotone with respect to the information ordering.

#### 3. CapSafety.thy — Capability System Safety

| Property | Value |
|----------|-------|
| File | [proof/CapSafety.thy](proof/CapSafety.thy) |
| Imports | `TritOps` |
| Lines | ~163 |
| Key definitions | `cap_check`, `cap_valid`, capability grant/revoke |
| Key theorems | Grant monotonicity (rights only narrow), revocation completeness, validity trichotomy, access control soundness |
| C correspondence | `src/syscall.c` — `kernel_cap_create`, `kernel_cap_grant`, `kernel_cap_revoke` |

**What it proves:** The capability system is **monotonically safe**: granting
a capability via Kleene AND can only narrow rights, never widen them.
Revoked capabilities have Neg validity and are unconditionally denied.
Unknown-validity capabilities are also denied (conservative access control).
Chained grants (grant-of-grant) are still bounded by the original parent.

#### 4. MemIsolation.thy — Memory Page Isolation

| Property | Value |
|----------|-------|
| File | [proof/MemIsolation.thy](proof/MemIsolation.thy) |
| Imports | `TritOps` |
| Lines | ~195 |
| Key definitions | `page` record, `page_fresh`, `page_alloc`, `page_free`, `page_clean` |
| Key theorems | Unknown-init guarantee, scrub-on-free, no-stale-data, page validity state machine, owner isolation |
| C correspondence | `src/memory.c` — `mem_init`, `mem_alloc`, `mem_free`, `mem_read`, `mem_write` |

**What it proves:** Fresh pages contain only Unknown trits (no information
leakage at allocation). Freed pages are scrubbed to Unknown (no cross-process
data leakage). The free→alloc cycle guarantees no stale data. Page validity
follows a strict state machine: Unknown (free) → Pos (allocated) → Unknown
(free) or Neg (reserved). Only the owning thread can access its pages.

#### 5. IPCCorrect.thy — IPC Message Integrity

| Property | Value |
|----------|-------|
| File | [proof/IPCCorrect.thy](proof/IPCCorrect.thy) |
| Imports | `TritOps` |
| Lines | ~193 |
| Key definitions | `ipc_msg`, `endpoint`, `ep_send`, `ep_recv`, `notification` |
| Key theorems | Send-recv integrity, endpoint state machine, unknown slot detection, notification atomicity |
| C correspondence | `src/ipc.c` — `ipc_send`, `ipc_recv`, `ipc_signal`, `ipc_wait` |

**What it proves:** Messages sent through IPC are received with exactly the
same payload (integrity). The endpoint state machine allows only valid
transitions (Idle↔SendBlocked, Idle↔RecvBlocked). The **ternary advantage**:
Unknown slots are distinguishable from zero-valued data slots, so receivers
can always determine how many words the sender actually wrote. Notifications
are consumed exactly once (signal-then-wait succeeds, double-wait fails).

#### 6. SecurityCIA.thy — CIA Triad with Ternary Capabilities

| Property | Value |
|----------|-------|
| File | [proof/SecurityCIA.thy](proof/SecurityCIA.thy) |
| Imports | `Main` (standalone trit definition using F/U/T naming) |
| Lines | ~245 |
| Key definitions | `capability` record (read/write/grant/valid), `cap_derive`, `cap_revoke`, `flow_allowed`, `write_allowed` |
| Key theorems | Authority confinement, derivation monotonicity, revocation finality, confidentiality (no read-up), integrity (no write-up), availability (no DoS), non-interference |
| C correspondence | `src/syscall.c` — full capability lifecycle |

**What it proves:** The complete CIA triad over ternary capabilities:
**Confidentiality** — secret (T-labeled) data cannot flow to public (F) or
classified (U) domains. **Integrity** — only high-integrity (T-label) threads
can write to all objects; low-integrity threads are restricted. **Availability**
— invalid (F-validity) capabilities cannot block operations by valid (T-validity)
holders. Cross-domain capability derivation is monotonically weakening.

#### 7. TranslationValidation.thy — Compiler Correctness

| Property | Value |
|----------|-------|
| File | [proof/TranslationValidation.thy](proof/TranslationValidation.thy) |
| Imports | `Main` (standalone trit definition using F/U/T naming) |
| Lines | ~208 |
| Key definitions | Source AST (`src_expr`), bytecode VM (`tgt_insn`), `compile`, `src_eval`, `tgt_step` |
| Key theorems | NOT involution, De Morgan, MUL commutativity/absorption, literal/variable compile correctness, translation soundness |
| C correspondence | `tools/compiler/` — lexer through codegen pipeline |

**What it proves:** The ternary compiler preserves semantics: every trit
operation in the source expression language has the same denotation after
compilation to bytecode. Specifically, literals compile to PUSH, variables
to LOAD, and all operators (AND, OR, NOT, MUL, DOT) have correct bytecode
sequences. Balanced ternary multiplication is commutative and Unknown-absorbing.

#### 8. TJSON_Validation.thy — Ternary JSON Validation

| Property | Value |
|----------|-------|
| File | [proof/TJSON_Validation.thy](proof/TJSON_Validation.thy) |
| Imports | `TritKleene`, `TritOps` |
| Lines | ~362 |
| Key definitions | `tjson_allOf`, `tjson_anyOf`, `tjson_not`, epistemic merge, diff comparison |
| Key theorems | allOf/anyOf lattice properties, composite validation soundness, epistemic merge correctness, diff comparison correctness, merge-strategy lattice |
| C correspondence | TJSON format implementation in `src/` |

**What it proves:** The three-valued TJSON validation system correctly
implements schema validation as a lattice operation. `allOf` (conjunction)
computes the meet, `anyOf` (disjunction) computes the join. Validation
results compose correctly under all Kleene logic laws. The epistemic merge
(confidence-aware AND) correctly handles Unknown-classified fields. Diff
comparison and merge strategies form a proper lattice.

---

## 8. Adding New Tests

### Step-by-Step Procedure

1. **Create the test file** in `tests/` (or the appropriate test directory):
   ```c
   /* tests/test_my_feature.c */
   #include "../include/set5/trit.h"
   /* ... includes ... */

   static int pass_count = 0, fail_count = 0;
   #define TEST(name) do { printf("  TEST: %s ... ", name); } while(0)
   #define PASS() do { printf("PASS\n"); pass_count++; } while(0)
   #define FAIL(msg) do { printf("FAIL: %s\n", msg); fail_count++; } while(0)

   /* ... test functions ... */

   int main(void) {
       printf("=== My Feature Tests ===\n");
       /* call test functions */
       printf("\n%d passed, %d failed, %d total\n",
              pass_count, fail_count, pass_count + fail_count);
       return fail_count > 0 ? 1 : 0;
   }
   ```

2. **Add build target** to root `Makefile`:
   ```makefile
   # ---- My Feature test suite ----
   test_my_feature: tests/test_my_feature.c $(COMMON_DEPS)
   	$(CC) $(CFLAGS) -o $@ $<
   ```

3. **Add to `SET5_TEST_BINS`** (existing variable near top of Makefile):
   ```makefile
   SET5_TEST_BINS += test_my_feature
   ```

4. **Add to `_run-test-suites`** target:
   ```makefile
   @echo "=== My Feature tests ==="
   @./test_my_feature || FAIL=1
   ```

5. **Add parser section** to `tools/test_grand_summary.sh` for the new suite.

6. **Add to `seT6/Makefile`** if it should be independently runnable.

7. **Run and verify:**
   ```bash
   make test6
   # Ensure ALL tests pass, including the new suite
   ```

8. **Update this document** — add the suite to the catalog in Section 4.

### Output Format Convention

All test suites must print output parseable by the grand summary script:
```
=== Suite Name ===
  TEST: test_name ... PASS
  TEST: test_name ... FAIL: reason
N passed, M failed, T total
```

---

## 9. Adding New Proofs

### Step-by-Step Procedure

1. **Create the theory file** in `proof/`:
   ```isabelle
   theory MyTheory
     imports TritOps    (* or TritKleene, or Main for standalone *)
   begin

   (* Your definitions and proofs *)

   end
   ```

2. **Add to session ROOT** file (`proof/ROOT`):
   ```
   session seT6_Proofs = HOL +
     description "seT6 Ternary Microkernel — Formal Verification Proofs"
     theories
       TritKleene
       TritOps
       ...existing...
       MyTheory        (* ← add here *)
   ```

3. **Verify the proof builds:**
   ```bash
   tools/isabelle build -d proof seT6_Proofs
   ```

4. **Update this document** — add the theory to the catalog in Section 7.

### Proof Style Guide

- **Import `TritOps`** when you need the full K₃ algebra (includes `TritKleene`).
- **Import `Main`** only for standalone theories that redefine `trit`.
- **Proof method:** Prefer exhaustive case splitting: `by (cases a; cases b) auto`.
  This is complete for all 9 (3×3) trit input combinations.
- **Header comment:** Include a block comment describing what the theory proves,
  which C source files it corresponds to, and the AFP basis.
- **Naming convention:** `snake_case` for definitions and lemmas.
  Prefix with the subsystem: `cap_`, `mem_`, `ipc_`, `trit_`, etc.
- **SPDX license:** Include `SPDX-License-Identifier: GPL-2.0` in the header.

### Proof ↔ Code Traceability

Every proof theory should document which C source files it verifies:

| Theory | C Source | Key Functions |
|--------|----------|---------------|
| TritKleene | `include/set5/trit.h` | `trit_and`, `trit_or`, `trit_not` |
| TritOps | `include/set5/trit.h` | All trit arithmetic |
| CapSafety | `src/syscall.c` | `kernel_cap_create`, `kernel_cap_grant`, `kernel_cap_revoke` |
| MemIsolation | `src/memory.c` | `mem_init`, `mem_alloc`, `mem_free` |
| IPCCorrect | `src/ipc.c` | `ipc_send`, `ipc_recv`, `ipc_signal` |
| SecurityCIA | `src/syscall.c` | Full capability lifecycle |
| TranslationValidation | `tools/compiler/` | Lexer → codegen pipeline |
| TJSON_Validation | `src/` | TJSON format handling |

---

## 10. Troubleshooting

### "isabelle: command not found"

Use the wrapper script instead of bare `isabelle`:
```bash
tools/isabelle version    # ✅ Correct
isabelle version          # ❌ May pick up wrong version
```

### Wrong Isabelle version (e.g., "Isabelle2024" instead of "Isabelle2025-2")

The system may have an older Isabelle on PATH. The `tools/isabelle` wrapper
hardcodes the correct path. Always use it:
```bash
bash tools/isabelle version
# Should print: Isabelle2025-2
```

If the symlink is broken:
```bash
ls -la Isabelle2025-2
# Should point to /opt/isabelle/Isabelle2025-2
# If broken, recreate:
ln -sfn /opt/isabelle/Isabelle2025-2 Isabelle2025-2
```

### Proof build fails with "Unknown theory"

Ensure the theory is listed in `proof/ROOT` and that its `imports` line
references an existing parent theory.

### Tests hang or segfault

Run with AddressSanitizer:
```bash
gcc -std=c11 -fsanitize=address,undefined -Iinclude -o /tmp/test tests/test_xxx.c
/tmp/test
```

### `make test6` reports missing suites

Check that all test binaries are listed in `SET5_TEST_BINS` and that
`_run-test-suites` has entries for each suite. The grand summary script
will report any missing suites explicitly.

---

## 11. Quality Standard

### Sigma 9 Requirement

Every commit must maintain **0 test failures** across all suites. This is
the **Sigma 9** quality standard referenced throughout the project:

- `make test6` → 0 failures, all suites present
- `tools/isabelle build -d proof seT6_Proofs` → all theories checked
- No compiler warnings (build with `-Wall -Wextra`)

### Before Committing

```bash
# 1. Run all tests
make test6

# 2. Verify proofs (if any proof files changed)
tools/isabelle build -d proof seT6_Proofs

# 3. Check for errors
make clean && make test6
```

### Continuous Integration

When CI is configured (TODO T-006), these checks will run automatically
on every push and pull request.

---

*This document is maintained as part of the seT6 Perpetual Development
Flywheel. See [TODOS.md](TODOS.md) for the active task list and
[DOCS_INDEX.md](DOCS_INDEX.md) for the full documentation index.*
