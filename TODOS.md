---
title: "seT6 Active TODO List"
date: 2026-02-17
schema: "PARA-GFM hybrid"
last_flywheel_cycle: 2026-02-19T00:00:00Z
total_items: 57
completed_items: 5
min_threshold: 10
batch_size: 5
---

# seT6 Active TODO List

> **Flywheel Rule:** Maintain 10–20 active items. When count drops below 10,
> trigger daily-search → regenerate cycle. Process in batches of 5.
> All items must reach Sigma 9 (0 errors, 100% pass) before marking `[DONE]`.

## Batch 1 — Critical Test Coverage (Value ≥ 8) ✅ COMPLETE

- [x] **T-001** Expand `test_ternary_database.c` from 4 → 32 tests: CRUD, CAM, RLE, Huffman, NULL propagation (STRICT/PROPAGATE/LENIENT), DB operations ✅ (Value: 9; Batch: 1/5)
- [x] **T-002** Create `tests/test_ai_acceleration.c` — 24 tests: BitNet quantize/forward, DLFET gates, sparse matrices, NN layers, activation ✅ (Value: 9; Batch: 1/5)
- [x] **T-003** Create `tests/test_fault_tolerant_network.c` — 25 tests: Hamming ECC (all 81 patterns + per-position correction), routing, consensus, packet encode/decode, NIC ✅ (Value: 9; Batch: 1/5)
- [x] **T-004** `tests/test_adversarial.c` — 34 tests: memory (OOB, double-free, UAF, OOM, readonly, reserved), IPC (destroyed ep, exhaustion, OOB), caps (no-grant, revoked, monotonicity, exhaustion), scheduler (exhaustion, double-destroy, invalid tid/priority), trit pack/unpack ✅ (Value: 8; Batch: 1/5)
- [x] **T-005** README.md updated: "Phase 8 — 1792+ tests passing across 34 suites" ✅ (Value: 8; Batch: 1/5)

## Batch 2 — Infrastructure & CI (Value ≥ 7)

- [ ] **T-006** Add GitHub Actions CI pipeline: `make test6` on push/PR, artifact upload of test logs, badge in README (Value: 9; Batch: 2/5)
- [ ] **T-007** Integrate AddressSanitizer (`-fsanitize=address,undefined`) build target: `make test-asan`; all 1681+ tests must pass clean (Value: 8; Batch: 2/5)
- [ ] **T-008** Add `gcov`/`lcov` code coverage: `make coverage` target, generate HTML report, establish baseline (Value: 7; Batch: 2/5)
- [ ] **T-009** Add kernel fuzz testing harness: libFuzzer or AFL-based, targeting IPC payload parsing, capability decode, trit arithmetic overflow (Value: 8; Batch: 2/5)
- [ ] **T-010** Create Dockerfile for reproducible builds: Ubuntu 24.04 base, all deps, `make test6` in container (Value: 7; Batch: 2/5)

## Batch 3 — Hardware Verification (Value ≥ 7)

- [ ] **T-011** Add Icarus Verilog testbenches for all 13 `.v` modules: compile with `iverilog`, simulate with `vvp`, assert signal correctness (Value: 8; Batch: 3/5)
- [ ] **T-012** Validate all 7 `.dts` device tree files with `dtc` compiler: `make dts-check` target (Value: 6; Batch: 3/5)
- [ ] **T-013** Create `hw/ternary_cpu_top.v` — top-level Verilog module integrating ALU + adder + multiplier + sense amp + TCAM into a minimal ternary CPU (Value: 8; Batch: 3/5)
- [ ] **T-014** Extend Isabelle proofs: add `TernaryArith.thy` for carry-lookahead adder correctness, `TCAMSearch.thy` for TCAM match semantics (Value: 7; Batch: 3/5)
- [ ] **T-015** Generate FPGA timing report stubs for Xilinx/Lattice targets from constraint files (Value: 6; Batch: 3/5)

## Batch 4 — seT6 Unique Modules (Value ≥ 7)

- [ ] **T-016** Implement `src/time_sync_daemon.c` — NTP-like ternary time synchronization for distributed seT6 nodes, Lamport clock with trit-valued drift (Value: 8; Batch: 4/5)
- [ ] **T-017** Implement `src/namespace_isolation.c` — process namespace isolation using ternary capabilities: mount/PID/net namespace fencing (Value: 8; Batch: 4/5)
- [ ] **T-018** Implement `src/audit_firewall.c` — ternary audit log + trit-granularity firewall rules (allow/deny/inspect) (Value: 7; Batch: 4/5)
- [ ] **T-019** Create performance regression benchmarks: `make bench` target tracking trit ops/sec, IPC latency, memory throughput across commits (Value: 7; Batch: 4/5)
- [ ] **T-020** Fix Trithon `pip install` path: add build backend to `pyproject.toml`, auto-build `libtrithon.so`, `make trithon-install` (Value: 6; Batch: 4/5)

## Batch 5 — Documentation & Ecosystem (Value ≥ 5)

- [ ] **T-021** Generate API reference with Doxygen: `make docs` target, HTML output in `docs/api/`, all 41 headers documented (Value: 6; Batch: 5/5)
- [ ] **T-022** Create CHANGELOG.md: conventional changelog format, backfill from `log.md` and git history (Value: 5; Batch: 5/5)
- [ ] **T-023** Write ternary network protocol RFC-style spec in `docs/protocols/T-NET-PROTOCOL.md`: frame format, trit encoding on wire, error correction (Value: 7; Batch: 5/5)
- [ ] **T-024** Research & integrate new ternary patents: search for RRAM ternary, memristive computing, carbon nanotube ternary gate patents filed 2024–2026 (Value: 8; Batch: 5/5)

## Batch 6 — Ternary Reversion Guards & Crown Jewel Protection (Value ≥ 8) 🔬

- [ ] **T-025** Create `tests/test_ternary_reversion_guard.c` — Crown Jewel pinning: Known-Answer-Test (KAT) vectors for all 11 crown jewel functions (trit_and/or/not Kleene truth tables, SIMD packed64, tcrypto round-trip, S-box, radix-3 FFT butterfly, Avizienis, Ingole TALU, GF(3) Hamming, Kleene NULL, TCAM 3-value match, trit_cast bridge). Each KAT hardcodes expected output — regression breaks it instantly. Must produce trits in full {-1,0,+1} range (not just {0,1}). (Value: 10; Batch: 6/5; Research: Binary reversion audit 2026-02-18)
- [ ] **T-026** Add `_Static_assert` compile-time guards in `trit.h`: Kleene truth table validation at compile time — `_Static_assert(trit_and(TRIT_UNKNOWN, TRIT_TRUE) == TRIT_UNKNOWN)` for all 9 pairs per operator. Add `TRIT_RANGE_CHECK` macro. (Value: 9; Batch: 6/5; Research: Binary reversion audit)
- [ ] **T-027** Upgrade `crypto_xorshift()` in `trit_crypto.c` to GF(3) LFSR PRNG — replace binary xorshift32 with ternary feedback shift register using trit_add_mod3 feedback polynomial. Verify uniform {-1,0,+1} distribution via chi-squared test in test suite. (Value: 9; Batch: 6/5; Research: Binary reversion audit + ternary CMOS papers)
- [ ] **T-028** Upgrade `ternary_huffman_build()`/`compress()` in `ternary_database.c` — replace binary Huffman codes `"0"/"10"/"11"` with base-3 Huffman using trit symbols. Replace uint8_t bitstream with trit-packed stream. Compress/decompress round-trip test must produce full trit range. (Value: 9; Batch: 6/5; Research: Binary reversion audit)
- [ ] **T-029** Upgrade `tcam_crossbar_search_dst()` in `hynix_tcam.c` — replace int {0,1} hit vector with trit-valued hit vector (TRIT_TRUE=match, TRIT_FALSE=mismatch, TRIT_UNKNOWN=don't-care), matching native TCAM semantics. (Value: 8; Batch: 6/5; Research: Binary reversion audit + Hynix patent)

## Batch 7 — Research-Aligned Ternary Upgrades (Value ≥ 7) 🧪

- [ ] **T-030** Align `ternary_weight_quantizer.c` with Spectra 1.1 / Sherry: add per-tensor symmetric quantization path and asymmetric 1.25-bit quantization. Add test vectors comparing against known BitNet b1.58 model outputs. (Value: 10; Batch: 7/5; Research: Spectra 1.1 + Sherry/Tencent papers)
- [ ] **T-031** Create `tests/test_trit_simd_regression.c` — exhaustive regression for trit_and_packed64/trit_or_packed64: all 32-trit word combinations, verify against scalar reference. Validates T-SAR finding that SIMD ternary is production-ready. (Value: 9; Batch: 7/5; Research: T-SAR SIMD LUT paper)
- [ ] **T-032** Align `trit_crypto.c` LWE lattice implementation with NIST FIPS 203 ML-KEM parameter sets (ML-KEM-512/768/1024). Prove lattice dimension/modulus alignment. Add Isabelle proof `LatticeCrypto.thy` for LWE hardness reduction in GF(3). (Value: 9; Batch: 7/5; Research: NIST FIPS 203 + seT6 crypto hardening)
- [ ] **T-033** Create `src/rram_ternary_cim.c` — RRAM ternary compute-in-memory emulator based on 2025 papers showing 91% energy reduction. Model crossbar array with trit-valued cells and MAC operations. Add hw/rram_ternary_cim.v Verilog. (Value: 8; Batch: 7/5; Research: RRAM CiM papers 2025)
- [ ] **T-034** Extend `fault_tolerant_network.c` with ReTern-inspired fault tolerance: add noise injection during ternary inference, verify graceful degradation (≤35% quality loss). Creates bridge between error correction and AI acceleration. (Value: 8; Batch: 7/5; Research: ReTern NeurIPS 2025)

## Batch 8 — Formal Verification Extensions (Value ≥ 7) 📐

- [ ] **T-035** Create `proof/TernaryArith.thy` — balanced ternary carry-lookahead adder correctness: ∀ a b ∈ T^n. decode(ternary_add(a,b)) = decode(a) + decode(b). Includes carry propagation lemma + overflow detection. (Value: 9; Batch: 8/5; Research: Existing T-014 + Avizienis crown jewel)
- [ ] **T-036** Create `proof/TCAMSearch.thy` — TCAM match semantics: ∀ key mask entry. tcam_match(key, mask, entry) ↔ (∀i. mask[i]=UNKNOWN ∨ key[i]=entry[i]). Soundness + completeness of 3-valued search. (Value: 8; Batch: 8/5; Research: T-014 + Hynix patent + reversion audit)
- [ ] **T-037** Create `proof/LatticeCrypto.thy` — LWE ternary hardness: ring-LWE over Z_q with ternary error distribution. SIS reduction for trit_crypto sponge hash. (Value: 8; Batch: 8/5; Research: NIST FIPS 203 alignment)
- [ ] **T-038** Create `proof/HuffmanTernary.thy` — base-3 Huffman optimality: ∀ trit distribution D. expected_length(huffman3(D)) ≤ H₃(D) + 1 where H₃ = ternary entropy. (Value: 7; Batch: 8/5; Research: Binary reversion guard for T-028)
- [ ] **T-039** Create `proof/SIMDPacked.thy` — packed64 trit correctness: ∀ i ∈ [0,31]. extract(trit_and_packed64(a,b), i) = trit_and(extract(a,i), extract(b,i)). Bitwise correspondence lemma. (Value: 7; Batch: 8/5; Research: T-SAR SIMD validation)

## Batch 9 — Standards Bridge & Ecosystem (Value ≥ 6) 🌐

- [ ] **T-040** Create `docs/protocols/PAM3-IEEE802.3-BRIDGE.md` — formal specification bridging seT6's PAM-3 transcoder to IEEE 802.3df PAM-4 standard. Define trit-to-PAM encoding, symbol mapping, link training adaptation. (Value: 8; Batch: 9/5; Research: IEEE 802.3df ratification)
- [ ] **T-041** Add TENET-style dataflow model in `hw/tenet_dataflow.v` — model the 21.1× efficient ternary MAC unit architecture for integration with existing ALU/multiplier modules. (Value: 7; Batch: 9/5; Research: TENET ASIC paper)
- [ ] **T-042** Create `src/ternary_snn.c` — ternary spiking neural network module inspired by CTSN: spike(+1), no-spike(0), inhibit(-1). Natural trit mapping. Test with XOR/timing benchmarks. (Value: 6; Batch: 9/5; Research: Ternary SNN papers 2025)
- [ ] **T-043** Upgrade `samsung_tseq.c` GF(2) LFSR to GF(3) LFSR wrapper: maintain patent-compliant binary core but add native ternary m-sequence generator using trit_add_mod3 feedback polynomial as seT6-native alternative. (Value: 7; Batch: 9/5; Research: Binary reversion audit)
- [ ] **T-044** Create `tests/test_binary_sentinel.c` — automated binary reversion detector: for each "at risk" function, assert outputs contain full trit range {-1,0,+1}, PRNG distribution is uniform over 3 values not 2, no implicit bool→trit flattening. Run as part of `make test6`. (Value: 9; Batch: 9/5; Research: Binary reversion audit)

---

**Total: 57 items (5 done, 52 remaining) | Batches: 12 (Batch 1 ✅) | Min threshold: 10 | Next flywheel: when < 10 remain**
**Research basis: DAILY_SEARCH_LOG_2026-02-18.md — 18 findings, 10 high-value**
**Gödel Machine basis: SET6_BECOMES_A_GODEL_MACHINE.md + DGM (github.com/jennyzzt/dgm) research**
**Ternary-first mandate: 8/9 HIGH-risk binary functions targeted for GF(3) upgrade**
**Crown jewel protection: 11 functions protected by KAT vectors in T-025**

## Batch 10 — Gödel Machine Core Module (Value ≥ 9) 🧠

> **Source:** SET6_BECOMES_A_GODEL_MACHINE.md (Schmidhuber 2003, DGM/Sakana AI 2025, HGM/Schmidhuber 2025)
> **Pattern:** Darwin Gödel Machine (github.com/jennyzzt/dgm) — evolutionary self-improvement via
> lineage tracking, LLM-driven code mutation, tiered fitness evaluation, archive selection.
> **Principle:** seT6 code rewrites occur ONLY if u(s_new, Env) > u(s_old, Env) + cost(rewrite).
> **Mac 128K analogy:** Just as System 1.0's 64KB ROM Toolbox + QuickDraw enabled an entire
> paradigm shift from 128KB RAM, seT6's Gödel module provides the self-referential proof engine
> that transforms a ternary OS into a provably self-improving system.

- [ ] **T-045** Create `src/godel_machine.c` — core Gödel machine engine implementing the 6 proof manipulation instructions as a C API: `godel_get_axiom(n)` retrieves the nth axiom from seT6's axiomatic system A (Isabelle .thy files), `godel_apply_rule(k,m,n)` applies inference rule k to theorems m and n, `godel_delete_theorem(m)` removes obsolete theorems post-rewrite, `godel_set_switchprog(m,n)` configures a code segment for replacement (maps to git diff application), `godel_check()` verifies the most recent theorem matches the self-improvement target, `godel_state2theorem(m,n)` encodes runtime state (test results, coverage, benchmark scores) as a new theorem. State representation s(t) = {src/*.c, tests/*, proof/*.thy, Makefile, test_results}. Utility function u(s,Env) = Σ(test_pass × proof_verified × trit_coverage). Includes BIOPS scheduler that allocates a tunable fraction of build time to improvement search. (Value: 10; Batch: 10/5; Research: Gödel Machine formal model, DGM self_improve_step.py)

- [ ] **T-046** Create `src/godel_utility.c` — utility metric calculator implementing the Sigma 9 composite score as the Gödel machine's reward function r(τ): `godel_utility_compute(state)` returns u = (tests_passing/tests_total) × (proofs_verified/proofs_total) × (trit_functions/total_functions) × (1 - binary_reversion_count/total_functions). Tracks delta utility per modification: Δu = u(s_new) - u(s_old). Includes cost accounting c(proof) = build_time_ms + test_time_ms + isabelle_time_ms. Self-improvement criterion: accept IFF Δu > c(proof)/normalization_constant. Implements DGM-style CMP (Cumulative Marginal Potential) from HGM for long-term benefit estimation. (Value: 10; Batch: 10/5; Research: Gödel utility function + HGM CMP metric)

- [ ] **T-047** Create `src/godel_proof_searcher.c` — BIOPS-inspired proof search engine: enumerates candidate C modifications ranked by Kolmogorov complexity proxy (shorter diffs first, simpler changes prioritized). Implements DGM's tiered evaluation pipeline adapted for C: Tier 1 `gcc -fsyntax-only` (compile check), Tier 2 `isabelle build` (proof gate — HARD REJECT if proofs break), Tier 3 `make test6` (unit tests), Tier 4 integration tests, Tier 5 full benchmarks. Each tier is a go/no-go gate — failure at any tier immediately rejects the candidate, implementing the Gödel machine's implicit rollback mechanism. Favors modifications aligned with the universal prior P(w) = 2^{-K(w)}. (Value: 10; Batch: 10/5; Research: BIOPS algorithm + DGM tiered evaluation)

- [ ] **T-048** Create `tools/godel_search.sh` — orchestration harness implementing the DGM outer evolutionary loop adapted for C/Isabelle: (1) `select_parent` — choose variant from archive using score_child_prop (score × 1/(1+children)), (2) `diagnose` — analyze `make test6` failure logs + Isabelle counterexamples to identify improvement candidates, (3) `mutate` — generate candidate C patch in sandboxed build environment, (4) `evaluate` — tiered: compile → proofs → tests → benchmarks, (5) `archive` — if u(s_new) > u(s_old) + cost, store variant with metadata {parent_id, diff, utility_score, generation, timestamp}, (6) `iterate` — resume from archived state. Maintains lineage via git branches (one branch per variant). Supports `--max-generations`, `--batch-size`, `--archive-mode=keep_better|keep_all`. (Value: 9; Batch: 10/5; Research: DGM DGM_outer.py + evo_utils.py)

- [ ] **T-049** Create `tests/test_godel_machine.c` — comprehensive test suite for the Gödel machine module: utility function computation (known inputs → expected score), delta utility tracking (modification → Δu > 0 required), cost accounting (build + test + proof time measurement), proof instruction API (get_axiom → valid axiom returned, apply_rule → valid theorem derived, delete_theorem → theorem removed, set_switchprog → diff staged, check → target matched/rejected, state2theorem → runtime state encoded), self-improvement criterion (accept only when Δu > cost), rollback on failed verification (state unchanged after rejection), archive operations (store/retrieve/select variants), lineage reconstruction (parent chain → sequential patches). Must pass at Sigma 9. (Value: 9; Batch: 10/5; Research: DGM tests/ + Gödel machine verification)

## Batch 11 — Gödel Machine Formal Verification (Value ≥ 8) 📐🧠

> **Source:** Gödel machine axiomatic system A (extension of Peano arithmetic)
> **Principle:** seT6's Isabelle proof system IS the formal verification engine that the Gödel
> machine uses to verify self-improvements. New proofs formalize the self-improvement process itself.
> **Addresses:** Gödel's 2nd incompleteness theorem limitation — we prove relative consistency
> rather than absolute consistency, just as the theoretical framework prescribes.

- [ ] **T-050** Create `proof/GoedelAxioms.thy` — Isabelle formalization of seT6's axiomatic system A extending Peano arithmetic with: (1) hardware axioms — trit state transitions (trit_and/or/not semantics from TritOps.thy, carry propagation from adder circuits), (2) reward axioms — test_pass(t) = +1, proof_verified(t) = +1, binary_reversion(t) = -1, build_failure(t) = -2, (3) environment axioms — build system response model (gcc + isabelle + make as deterministic environment), (4) utility definition — u(s,Env) = Σ_{τ=t}^{T} r(τ) formalized as nat → int summation, (5) initial state s(1) axiom — encodes seT6 baseline (1792 tests, 34 suites, 8 proofs). (Value: 9; Batch: 11/5; Research: Gödel machine axiomatic system + existing proof/*.thy)

- [ ] **T-051** Create `proof/SelfImprovement.thy` — Isabelle proof of the self-improvement criterion: theorem `self_improve_sound`: ∀ patch p, state s. u(apply_patch(s,p), Env) > u(s, Env) + cost(p) → accept(p). Includes lemmas: `utility_monotone` (accepted patches never decrease utility), `cost_bounded` (proof search cost is bounded by runtime fraction allocation), `rollback_safe` (rejected patches leave state unchanged). Encodes the Gödel machine's core guarantee that only provably beneficial modifications are applied. (Value: 9; Batch: 11/5; Research: Gödel machine self-improvement theorem)

- [ ] **T-052** Create `proof/GoedelSoundness.thy` — Isabelle meta-proof of proof system soundness preservation: theorem `switchprog_sound`: if A ⊢ φ before set_switchprog and A' is the updated axiom set (with new hardware axioms for modified code), then A' is consistent relative to A. Addresses Gödel's 2nd incompleteness theorem by proving RELATIVE consistency (A' consistent if A consistent) rather than absolute consistency. Includes `axiom_extension_conservative` lemma (new axioms don't contradict existing ones). (Value: 8; Batch: 11/5; Research: Gödel 2nd incompleteness + relative consistency)

- [ ] **T-053** Create `proof/GoedelUtility.thy` — Isabelle formalization of the utility function and optimization goal: defines u(s,Env) = E_μ[Σr(τ)] over seT6's deterministic build environment (no stochastic component since compilation and proofs are deterministic). Proves `utility_computable` (u is total and computable for any finite state), `utility_decomposable` (u(s) = u_tests(s) + u_proofs(s) + u_trit(s)), `improvement_transitive` (if u(s₁) > u(s₀) and u(s₂) > u(s₁) then u(s₂) > u(s₀) — lineage improvements compose). (Value: 8; Batch: 11/5; Research: Gödel utility function + deterministic environment simplification)

## Batch 12 — Gödel Machine Infrastructure & DGM Integration (Value ≥ 7) 🔧🧠

> **Source:** DGM implementation patterns (github.com/jennyzzt/dgm) adapted for C/Isabelle
> **Principle:** DGM's empirical mutation + evaluation loop, gated by Isabelle formal proofs,
> implements a practical Gödel machine that is both theoretically grounded AND empirically validated.
> **Mac 128K pattern:** Like System 1.0's Toolbox provided a complete palette (QuickDraw, Font
> Manager, Window Manager, Menu Manager), seT6's Gödel infrastructure provides the complete
> self-improvement palette: diagnostics, mutation, evaluation, archival, lineage, documentation.

- [ ] **T-054** Create `tools/godel_diagnose.sh` — DGM-inspired diagnostic engine (maps to DGM's `diagnose_improvement_prompt.py`): parses `make test6` failure logs and `isabelle build` error output, identifies: (a) failed test functions with stack traces, (b) Isabelle proof failures with counterexamples, (c) binary reversion indicators (functions outputting only {0,1}), (d) coverage gaps. Outputs structured JSON: `{log_summary, failing_tests[], proof_failures[], binary_reversions[], improvement_candidates[], priority_scores[]}`. Feeds into godel_search.sh step 2. (Value: 8; Batch: 12/5; Research: DGM diagnose_improvement_prompt.py)

- [ ] **T-055** Create `src/godel_archive.c` — variant archive manager (maps to DGM's `evo_utils.py`): tracks lineage of seT6 variants as git branches with metadata. API: `archive_store(variant_id, parent_id, utility_score, diff_path, generation)`, `archive_select_parent(method)` with methods {random, score_prop, score_child_prop, best}, `archive_get_lineage(variant_id)` returns ordered list of ancestor diffs for reconstruction, `archive_get_fitness(variant_id)` returns multi-objective vector [compiles, proofs_pass, tests_pass, trit_coverage, benchmark_ns]. Persists to `godel_archive.jsonl`. (Value: 8; Batch: 12/5; Research: DGM evo_utils.py + metadata.jsonl)

- [ ] **T-056** Create `GODEL_MACHINE_SPEC.md` — formal specification document mapping all Gödel machine theoretical concepts to concrete seT6 implementations: State s(t) = git repo at commit t, Utility u = Sigma 9 composite, Axioms A = proof/*.thy, Proof instructions = C API in godel_machine.c, switchprog = `git apply`, check = `make test6 && isabelle build`, Environment = {gcc, isabelle, make, test harness}. Includes Mac 128K-inspired feature inventory: 20 Gödel Machine "applications" (self-improving scheduler, self-optimizing memory allocator, auto-tuning trit SIMD, etc.), 20 "system functions" (utility calculator, proof searcher, archive manager, etc.), 20 "use cases" (ternary OS kernel self-optimization, proof-guided bug fixing, automated crown jewel hardening, etc.). (Value: 7; Batch: 12/5; Research: SET6_BECOMES_A_GODEL_MACHINE.md Mac 128K analogy)

- [ ] **T-057** Create `src/godel_mutable_zones.c` — mutation scope controller (maps to DGM's constrained editing): defines which source files/functions are MUTABLE (scheduler heuristics, allocator policies, compression parameters, benchmark tuning) vs IMMUTABLE (crown jewels from T-025: Kleene K₃ logic, SIMD packed64, tcrypto core, GF(3) Hamming, Isabelle-verified invariants). Implements a `zone_check(filepath, function_name)` API returning MUTABLE/IMMUTABLE/RESTRICTED. RESTRICTED zones allow modification only with additional proof obligations. Enforces DGM-style Docker/chroot sandboxing for all mutation attempts. Integrates with godel_search.sh to reject patches touching immutable zones. (Value: 7; Batch: 12/5; Research: DGM sandbox pattern + crown jewel protection T-025)

- [ ] **T-058** Extend Makefile with Gödel machine targets: `make godel-evaluate` computes multi-objective fitness vector [compiles, proofs_pass, tests_pass, trit_coverage, benchmark_score] and outputs JSON to `godel_fitness.json`. `make godel-search` runs one generation of the evolutionary loop. `make godel-diagnose` runs the diagnostic engine. `make godel-archive` displays current archive state and lineage. Wire test_godel_machine into `make test6`. (Value: 7; Batch: 12/5; Research: DGM Makefile patterns + existing Makefile structure)
