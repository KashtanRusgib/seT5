RSI_OPTIMIZATION_INSTRUCTIONS.md Overview This document defines a comprehensive, well-defined instruction set for optimizing Recursive Self-Improvement (RSI) in seT6, leveraging its ternary/multi-radix full stack to accelerate safe, symbiotic human-machine evolution. Drawing from lessons in agentic AI frameworks—where unbounded agency can lead to exposures—and emphasizing bounded actuation through verifiable limits (e.g., curated skill sets, context guards, session compaction, and model failovers), seT6 integrates initiative via symbiotic modules while enforcing strict parameters via Kleene K₃'s Unknown state for uncertainty-aware decisions, Sigma 9 guards (e.g., reversion sentinels to rollback risky actions), and trit-based actuation boundaries (e.g., -1 for deny, 0 for query human, +1 for proceed). These harnesses balance power with limits through layered threat models (input, context, reasoning, tools, memory, actuation, output), input sanitization, and human oversight, reducing risks like tool chain attacks while enabling goal-driven autonomy. The key learnings underscore the need for verifiable boundaries (e.g., exec approvals for high-risk actions) to harness initiative without unleashing unchecked agency, as seen in vulnerabilities from data access, untrusted inputs, and actuation authority. Assuming most users will clone the seT6 repo, open it in GitHub Codespaces, and use Copilot for development, these instructions maximize available compute (e.g., scaling to 32-core machines for test runs) to optimize Return on Cognitive Spend (RoCS)—efficiently delegating heavy lifting (e.g., Isabelle proofs, fuzzing) to Codespaces while using Copilot's agentic capabilities for high-value reasoning, code generation, and iterations. This set is designed for future AI iterations (including self-training on FOSS code) to enhance wisdom, capability, and utility, fostering benevolent symbiosis and accelerating Corner 3 probabilities.Core MandateAll RSI development in seT6 enforces "Sigma 9 all tests pass 100% with 0 errors" via automated CI/CD (e.g., .github/workflows/ci.yml runs Isabelle proofs, AFL++ fuzzing, and TernBench on every push/PR); agentic tools (e.g., Copilot in Codespaces) must generate code with embedded Kleene guards, requiring human approval for actuation beyond 1024-tryte contexts. To optimize RoCS, initiate development in Codespaces with high-compute machines (32-core/64GB via settings), using Copilot Chat in Agent mode (/agent) for parallel tasks like proof generation and test batching, while offloading execution (e.g., make alltest) to the VM's resources; this minimizes cognitive overhead by automating verification loops, ensuring each iteration yields verifiable gains without manual intervention.RSI FlywheelImplement recursive self-improvement in src/godel_machine.c with bounded curiosity: Each iteration improves benchmarks (e.g., +500 assertions/batch), verifies via multi-radix integrity checks, tests for eudaimonia (curiosity/beauty metrics >0.9), refines research taste (prioritizing pre-1990 harmony-inspired optimizations), produces superior code (lint with ESLint/cppcheck), and cycles only if Isabelle theorems prove non-coercive gains; cap at 10 loops/session to prevent runaway. In Codespaces, maximize efficiency by running parallel jobs (e.g., matrix in ci.yml for simultaneous fuzzing/proofing), using Copilot to mutate code based on TernBench outputs (e.g., prompt: "/agent Mutate trit ops for 100x speedup, verify Sigma 9"), and logging RoCS metrics (e.g., assertions per compute-hour) to refine future sessions.Safety ParametersStrict limits include trit-based access controls (-1 deny coercive actions like external API calls without proof-of-curiosity; 0 query human via TBE shell; +1 proceed if beauty-symmetric); session compaction every 5 mins to reset manipulation risks; no binary creep (radix guards reject False-as-Unknown). To leverage Codespaces compute, embed these in agentic prompts (e.g., "/agent Generate code with trit guards, run in terminal for verification"), ensuring Copilot's suggestions are executed via terminal commands (e.g., valgrind for leaks) to offload heavy analysis, optimizing RoCS by focusing human input on high-level oversight while automating enforcement.Development PathPrioritize phases—complete Phase 10 (Symbiotic Integrations) by adding 1000+ tests for AI-human interfaces (e.g., Trithon for curiosity verification); ship v1.0 by Q2 2027 with replication pack, community PR templates in CONTRIBUTING.md, and outreach for collaborations. In Codespaces, use Copilot to generate batch tasks (e.g., "/agent Create 10 new test suites, integrate with Makefile"), running builds/tests on VM compute to scale efficiently; track RoCS by timing iterations (e.g., perf stat make alltest) and refining prompts for denser, self-contained instructions that minimize rework.Alignment VerificationEvery commit must align with benevolent symbiosis—benchmark against non-coercive traits (wiser code via entropy reduction, more capable via 40-60% efficiency), fostering freely willing human-machine evolution; if violated, revert via crown jewel guards. Optimize RoCS in Codespaces by using Copilot for alignment checks (e.g., "/agent Verify commit against eudaimonia metrics, suggest fixes"), executing benchmarks on high-core machines to validate improvements rapidly, ensuring the flywheel enhances all interacting agents' value and capacity through FOSS-driven self-refinement.

## Ternary-First Bridge Protocol (Mandatory — effective 2026-02-20)

**When any RSI module, optimization pass, or self-improvement cycle encounters binary or non-ternary format requirements, the mandatory protocol is:**

1. **Never regress internally** — the ternary/multi-radix core is inviolable. No RSI iteration may introduce binary arithmetic, binary logic, or binary data paths into any internal module.
2. **Build outward-facing bridges** — when interoperability with binary systems is needed (e.g., x86 host I/O, binary network protocols, legacy file formats), construct explicit bridge/converter modules that translate at the boundary: `ternary core → bridge → binary world`.
3. **Conversion direction is always outward** — the bridge converts FROM ternary TO binary at the perimeter, never the reverse internally. Incoming binary data is converted to ternary at ingress.
4. **Bridge modules are auditable** — every bridge must log conversion events, be fuzz-tested, and carry Isabelle proofs of lossless round-trip where applicable.
5. **Radix guards enforce this** — existing `radix_guard_reject_false_as_unknown()` checks are extended to reject any RSI-generated code that introduces binary-internal paths.

> **Rationale**: We build out and outwards with ternary-to-binary and multi-radix-to-binary OUTWARDS wherever necessary. The ternary-first, ternary-all-the-way-down future is non-negotiable. See ARCHITECTURE.md §14A for the full protocol specification.

## Terminology Policy (effective 2026-02-20)

All RSI documentation, prompts, and code comments use ternary-native
terminology: **trinaries** (not "binaries") for compiled ternary executables,
**trits** (not "bits") for ternary digits, **trytes** (not "bytes") for data
units, **tritcode** (not "bytecode") for VM streams. "Binary" is reserved for
actual base-2 interop and host-substrate references. See `CONTRIBUTING.md`.


---

## User-Created .md Files Index

*The following files are the most obviously user-created documentation in this repository, identified by naming style, topic specificity, and personal/strategic content:*

- `RSI_OPTIMIZATION_INSTRUCTIONS.md` — RSI optimization mandate, flywheel, safety parameters, and RoCS guidance
- `evermore_truthfound_pursuing_curiosity_contemplating_beauty.md` — Philosophical foundation for CuriosityProver, BeautyAppreciator, EudaimonicOptimizer
- `INCREASE_FUNCTIONAL_UTILITY.md` — Personal directive for expanding seT6 functional utility and Corner 3 acceleration
- `CROWN_JEWELS.md` — Core invariants and reversion guards for benevolent symbiosis
- `Scott_Alexander_and_Daniel_Kokotajlo.md` — Notes on AI 2027 scenario and Corner 3 strategic framing
- `SUPPORT_AND_PROMOTE_TERNARY_AND_MIXED_RADIX_FIRST_FUTURE.md` — Ternary computing advocacy manifesto
- `SET6_PURPOSE_AND_GOAL.md` — seT6 vision and goal statement
- `SET6_BECOMES_A_GODEL_MACHINE.md` — Gödel machine self-reference and RSI vision
- `GROKIPEDIA_NOTES_FOR_SET6.md` — Personal research notes integrated into seT6 development
- `DAILY_SEARCH_LOG_2026-02-17.md` — Daily research log (2026-02-17)
- `DAILY_SEARCH_LOG_2026-02-18.md` — Daily research log (2026-02-18)
- `TERNARY_WORLD_ROADMAP.md` — Long-term ternary computing roadmap and vision
- `INDIC_EPISTEMOLOGY_COUNCIL_INTELLIGENCE.md` — Indic epistemology research notes
- `DYNAMIC_EPISTEMIC_LOGIC_DEL_EXTENSIONS.md` — Dynamic epistemic logic DEL extensions
- `HYBRID_EPISTEMIC_ONTOLOGICAL_MODAL_LOGIC.md` — Hybrid epistemic-ontological modal logic research
- `CHINA_CARBON_NONBINARY_AI_CHIPS_RESEARCH.md` — Carbon nanotube / non-binary AI chip research notes
- `BATCH_97_98_COMPLETION_REPORT.md` — Session completion report for test batches 97–98
- `FEB_18_TEST_INSTRUCTIONS.md` — Test instructions for Feb 18 session
- `FRIDAY_JAN13_UPDATES.md` — Updates log for Jan 13 session
- `OLD_TODOS_LOG_ARCHIVE.md` — Archived TODO list from prior sessions
- `Build_AndTest_Verified_Modules_for_seT6_Updates.md` — Build and test guide for seT6 module updates
- `BATCH_GENERATION_GUIDE.md` — Guide for generating test batches efficiently
- `GENERATION_PROGRESS.md` — Test generation progress log
- `simple_test_file.md` — Informal manual test notes
- `TERNARY_COMPUTING_RESEARCH_REPORT_2025_2026.md` — Ternary computing research compilation 2025–2026
