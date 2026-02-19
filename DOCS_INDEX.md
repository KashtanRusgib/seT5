---
title: "seT6 Documentation Index"
date: 2026-02-17
auto_generated: true
total_documents: 53
---

# seT6 Documentation Index

> Auto-generated master index of all `.md` files. Regenerate with:
> `find . -name '*.md' -not -path './.git/*' -not -path './Isabelle2025-2/*' -not -path './replication_pack/*' | sort`

---

## Root — Project Orientation & Design

| Document | Purpose |
|----------|---------|
| [README.md](README.md) | Master documentation — project overview, build, test instructions |
| [ARCHITECTURE.md](ARCHITECTURE.md) | Full microkernel architecture (16 sections) |
| [TODOS.md](TODOS.md) | **Active TODO list** (flywheel-managed, 24 items) |
| [TODOLIST.md](TODOLIST.md) | Legacy phase-based roadmap (Phases 0–5, mostly complete) |
| [OLD_TODOS_LOG_ARCHIVE.md](OLD_TODOS_LOG_ARCHIVE.md) | Archived completed/deferred TODOs |
| [SET6_PURPOSE_AND_GOAL.md](SET6_PURPOSE_AND_GOAL.md) | seT6 mission statement and goals |
| [BUILD_TO_FIT.md](BUILD_TO_FIT.md) | Build-to-fit methodology |
| [SOLUTIONS_RESOURCES.md](SOLUTIONS_RESOURCES.md) | Reference resources and solutions |
| [log.md](log.md) | Development log |

## Root — Design Specifications

| Document | Purpose |
|----------|---------|
| [INCREASE_FUNCTIONAL_UTILITY.md](INCREASE_FUNCTIONAL_UTILITY.md) | Phase 6 design spec (8 capability layers) |
| [FRIDAY_JAN13_UPDATES.md](FRIDAY_JAN13_UPDATES.md) | Phase 7 design spec (STT-MRAM, T-IPC, TFS) |
| [LOGICAL_ENHANCEMENTS_FOR_TRIT_LINUX.md](LOGICAL_ENHANCEMENTS_FOR_TRIT_LINUX.md) | 6 Trit Linux enhancement specifications |
| [INITIAL_PROJECT_QUESTIONS.md](INITIAL_PROJECT_QUESTIONS.md) | Initial project Q&A |

## Root — Patent Analysis

| Document | Patent | Vendor |
|----------|--------|--------|
| [HUAWEI_2025_TERNARY_CHIP_PATENT_CN119652311A.md](HUAWEI_2025_TERNARY_CHIP_PATENT_CN119652311A.md) | CN119652311A | Huawei |
| [SAMSUNG_PATENT_US11170290B2.md](SAMSUNG_PATENT_US11170290B2.md) | US11170290B2 | Samsung |
| [samsung_patent_CN105745888A.md](samsung_patent_CN105745888A.md) | CN105745888A | Samsung |
| [Intel_Loihi_WO2016199157A1.md](Intel_Loihi_WO2016199157A1.md) | WO2016199157A1 | Ingole (TALU) |
| [TSMC_TMD_INTEL_PAM_HYNIX_TCAM_patents.md](TSMC_TMD_INTEL_PAM_HYNIX_TCAM_patents.md) | Multiple | TSMC/Intel/Hynix |
| [MEGA_PATENT_ALIGNMENT_PACK.md](MEGA_PATENT_ALIGNMENT_PACK.md) | Combined | All vendors |

## Root — Research & Theory

| Document | Purpose |
|----------|---------|
| [seL4_whitepaper_and_reviews.md](seL4_whitepaper_and_reviews.md) | seL4 foundation review |
| [seT5_FORMAL_VERIFICATION_REPORT.md](seT5_FORMAL_VERIFICATION_REPORT.md) | Formal verification report |
| [CHINA_CARBON_NONBINARY_AI_CHIPS_RESEARCH.md](CHINA_CARBON_NONBINARY_AI_CHIPS_RESEARCH.md) | Chinese ternary chip research |
| [DYNAMIC_EPISTEMIC_LOGIC_DEL_EXTENSIONS.md](DYNAMIC_EPISTEMIC_LOGIC_DEL_EXTENSIONS.md) | DEL logic extensions |
| [HYBRID_EPISTEMIC_ONTOLOGICAL_MODAL_LOGIC.md](HYBRID_EPISTEMIC_ONTOLOGICAL_MODAL_LOGIC.md) | Hybrid modal logic |
| [INDIC_EPISTEMOLOGY_COUNCIL_INTELLIGENCE.md](INDIC_EPISTEMOLOGY_COUNCIL_INTELLIGENCE.md) | Epistemology research |
| [Truncated_ternary_notes.md](Truncated_ternary_notes.md) | Truncated ternary research |
| [GROKIPEDIA_NOTES_FOR_SET6.md](GROKIPEDIA_NOTES_FOR_SET6.md) | seT6 design notes |
| [seT5_Formal_Paper.md](seT5_Formal_Paper.md) | Formal paper draft |

## Root — Flywheel & Operations

| Document | Purpose |
|----------|---------|
| [DAILY_SEARCH_LOG_2026-02-17.md](DAILY_SEARCH_LOG_2026-02-17.md) | Daily search log |
| [TERNARY_WORLD_ROADMAP.md](TERNARY_WORLD_ROADMAP.md) | Ternary ecosystem roadmap |
| [ANALYSIS_OF_TEST_SUITE_CODE.md](ANALYSIS_OF_TEST_SUITE_CODE.md) | Test suite code analysis |
| [Build_AndTest_Verified_Modules_for_seT6_Updates.md](Build_AndTest_Verified_Modules_for_seT6_Updates.md) | Build/test verification guide |

## Root — Formal Verification & Proofs

| Document | Purpose |
|----------|----------|
| [TESTS_AND_PROOFS_INSTRUCTIONS.md](TESTS_AND_PROOFS_INSTRUCTIONS.md) | Comprehensive guide to all Isabelle/HOL proofs, test suites, and formal verification workflow |
| [seT5_FORMAL_VERIFICATION_REPORT.md](seT5_FORMAL_VERIFICATION_REPORT.md) | Formal verification report |
| [proof/](proof/) | 8 Isabelle/HOL theories (TritKleene, TritOps, CapSafety, MemIsolation, IPCCorrect, SecurityCIA, TranslationValidation, TJSON_Validation) |

### Proof Tooling

| Tool | Location | Purpose |
|------|----------|---------|
| `tools/isabelle` | [tools/isabelle](tools/isabelle) | Wrapper script for Isabelle2025-2 (hardcoded to `/opt/isabelle/Isabelle2025-2`) |
| `Isabelle2025-2/` | Symlink → `/opt/isabelle/Isabelle2025-2` | Isabelle2025-2 installation (gitignored) |

## docs/ — Patent Integration Guides

| Document | Patent | Vendor |
|----------|--------|--------|
| [docs/HUAWEI_CN119652311A_INTEGRATION.md](docs/HUAWEI_CN119652311A_INTEGRATION.md) | CN119652311A | Huawei |
| [docs/SAMSUNG_US11170290B2_INTEGRATION.md](docs/SAMSUNG_US11170290B2_INTEGRATION.md) | US11170290B2 | Samsung |
| [docs/SAMSUNG_CN105745888A_INTEGRATION.md](docs/SAMSUNG_CN105745888A_INTEGRATION.md) | CN105745888A | Samsung |
| [docs/TSMC_TMD_INTEGRATION.md](docs/TSMC_TMD_INTEGRATION.md) | TSMC TMD | TSMC |
| [docs/INTEL_PAM3_DECODER_INTEGRATION.md](docs/INTEL_PAM3_DECODER_INTEGRATION.md) | Intel PAM-3 | Intel |
| [docs/HYNIX_TCAM_INTEGRATION.md](docs/HYNIX_TCAM_INTEGRATION.md) | Hynix TCAM | SK Hynix |
| [docs/INGOLE_WO2016199157A1_INTEGRATION.md](docs/INGOLE_WO2016199157A1_INTEGRATION.md) | WO2016199157A1 | Ingole |

## docs/ — Subdirectories

| Directory | Purpose | Contents |
|-----------|---------|----------|
| [docs/patents/](docs/patents/) | Raw/summarized patent documents | *(empty — populate from searches)* |
| [docs/papers/](docs/papers/) | Academic papers | *(empty — populate from searches)* |
| [docs/protocols/](docs/protocols/) | Protocol specifications | *(empty — T-023 will add T-NET-PROTOCOL.md)* |

## seT6/ — Fork-Specific Documents

| Document | Purpose |
|----------|---------|
| [seT6/README.md](seT6/README.md) | seT6 fork overview |
| [seT6/ARCHITECTURE.md](seT6/ARCHITECTURE.md) | seT6-specific architecture |
| [seT6/TODOLIST.md](seT6/TODOLIST.md) | seT6 legacy phase roadmap |
| [seT6/FRIDAY_JAN13_UPDATES.md](seT6/FRIDAY_JAN13_UPDATES.md) | seT6 Friday updates |
| [seT6/INCREASE_FUNCTIONAL_UTILITY.md](seT6/INCREASE_FUNCTIONAL_UTILITY.md) | seT6 functional utility spec |
| [seT6/LOGICAL_ENHANCEMENTS_FOR_TRIT_LINUX.md](seT6/LOGICAL_ENHANCEMENTS_FOR_TRIT_LINUX.md) | seT6 Trit Linux enhancements |
| [seT6/SOLUTIONS_RESOURCES.md](seT6/SOLUTIONS_RESOURCES.md) | seT6 resources |
| [seT6/SET6_RND_INTEGRATION_ROADMAP.md](seT6/SET6_RND_INTEGRATION_ROADMAP.md) | R&D integration roadmap |
| [seT6/TESTS_GLOSSARY_OF_ALL_TESTS.md](seT6/TESTS_GLOSSARY_OF_ALL_TESTS.md) | Test glossary |

## tools/compiler/ — Ternary-C-Compiler Docs

| Document | Purpose |
|----------|---------|
| [tools/compiler/README.md](tools/compiler/README.md) | Compiler overview |
| [tools/compiler/docs/ARCHITECTURE.md](tools/compiler/docs/ARCHITECTURE.md) | Compiler architecture |
| [tools/compiler/docs/AGENT_PROMPT.md](tools/compiler/docs/AGENT_PROMPT.md) | AI agent prompt |
| [tools/compiler/docs/BEST_PRACTICES.md](tools/compiler/docs/BEST_PRACTICES.md) | Coding best practices |
| [tools/compiler/docs/CODE_OF_CONDUCT.md](tools/compiler/docs/CODE_OF_CONDUCT.md) | Code of conduct |
| [tools/compiler/docs/CONTRIBUTING.md](tools/compiler/docs/CONTRIBUTING.md) | Contributing guide |
| [tools/compiler/docs/LOGGING.md](tools/compiler/docs/LOGGING.md) | Logging guide |
| [tools/compiler/docs/README.md](tools/compiler/docs/README.md) | Docs readme |
| [tools/compiler/docs/TESTING.md](tools/compiler/docs/TESTING.md) | Testing guide |
| [tools/compiler/docs/TODOLIST.md](tools/compiler/docs/TODOLIST.md) | Compiler todo list |

---

**Total: 55 documents | Last generated: 2026-02-18**
