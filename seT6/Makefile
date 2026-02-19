# seT6 — Makefile
# Runs the FULL seT6 test suite (all seT5 base tests plus seT6 additions).
#
# Usage:
#   make test       — run every test suite (30+ suites, grand summary)
#   make <binary>   — build a single test binary (e.g. make test_ingole_wo2016199157a1)
#   ./<binary>      — run a single test binary directly
#
# All source lives in the seT5 root tree.  This Makefile delegates to
# the root Makefile which contains every build rule, then runs the
# grand summary.  The test6 convenience target at the root level
# invokes `make -C seT6 test`, so `make test6` from the project root
# is equivalent to `make test` from this directory.
#
# SPDX-License-Identifier: GPL-2.0

ROOT_DIR := $(realpath $(dir $(lastword $(MAKEFILE_LIST)))/..)

# ──────────────────────────────────────────────────────────────────────
# Default / help
# ──────────────────────────────────────────────────────────────────────
.PHONY: help
help:
	@echo ""
	@echo "  seT6 Test Runner"
	@echo "  ════════════════"
	@echo ""
	@echo "  make test              Run ALL test suites with grand summary"
	@echo "  make test-individual   List every individual test target"
	@echo "  make <target>          Build & run one suite (delegated to root)"
	@echo ""

# ──────────────────────────────────────────────────────────────────────
# Master test target — the ONE command that runs ALL tests.
#
#   make test     (from seT6/)
#   make test6    (from project root)
#
# Delegates to root Makefile which:
#   1. Force-deletes and recompiles every test binary
#   2. Runs every suite live with streaming output
#   3. Pipes output through tools/test_grand_summary.sh
#   4. Exits non-zero if ANY test fails
# ──────────────────────────────────────────────────────────────────────
.PHONY: test
test:
	$(MAKE) -C "$(ROOT_DIR)" test

# ──────────────────────────────────────────────────────────────────────
# Individual suite targets — each builds and runs exactly one suite.
# These let users run a single suite in isolation:
#
#   cd seT6 && make test-huawei
#   cd seT6 && make test-ingole
#   cd seT6 && make test-database
#   etc.
# ──────────────────────────────────────────────────────────────────────

.PHONY: test-compiler
test-compiler:
	$(MAKE) -C "$(ROOT_DIR)" build-compiler
	$(MAKE) -C "$(ROOT_DIR)/tools/compiler" $(addprefix run-,test_trit test_parser test_codegen test_vm test_typechecker test_linker test_selfhost test_arrays) 2>/dev/null || \
	  (cd "$(ROOT_DIR)/tools/compiler" && for t in test_trit test_parser test_codegen test_vm test_typechecker test_linker test_selfhost test_arrays test_hardware test_basic; do \
	    if [ -f ./$$t ]; then echo "[RUN] $$t"; ./$$t && echo "[PASS] $$t" || echo "[FAIL] $$t"; fi; \
	  done)

.PHONY: test-native
test-native:
	$(MAKE) -C "$(ROOT_DIR)" set5_native && "$(ROOT_DIR)/set5_native"

.PHONY: test-integration
test-integration:
	$(MAKE) -C "$(ROOT_DIR)" test_integration && "$(ROOT_DIR)/test_integration"

.PHONY: test-sel4
test-sel4:
	$(MAKE) -C "$(ROOT_DIR)" test_sel4_ternary && "$(ROOT_DIR)/test_sel4_ternary"

.PHONY: test-memory
test-memory:
	$(MAKE) -C "$(ROOT_DIR)" test_memory_safety && "$(ROOT_DIR)/test_memory_safety"

.PHONY: test-scheduler
test-scheduler:
	$(MAKE) -C "$(ROOT_DIR)" test_scheduler_concurrency && "$(ROOT_DIR)/test_scheduler_concurrency"

.PHONY: test-tbe
test-tbe:
	$(MAKE) -C "$(ROOT_DIR)" test_tbe && "$(ROOT_DIR)/test_tbe"

.PHONY: test-huawei
test-huawei:
	$(MAKE) -C "$(ROOT_DIR)" test_huawei_cn119652311a && "$(ROOT_DIR)/test_huawei_cn119652311a"

.PHONY: test-samsung-us
test-samsung-us:
	$(MAKE) -C "$(ROOT_DIR)" test_samsung_us11170290b2 && "$(ROOT_DIR)/test_samsung_us11170290b2"

.PHONY: test-samsung-cn
test-samsung-cn:
	$(MAKE) -C "$(ROOT_DIR)" test_samsung_cn105745888a && "$(ROOT_DIR)/test_samsung_cn105745888a"

.PHONY: test-tsmc-intel-hynix
test-tsmc-intel-hynix:
	$(MAKE) -C "$(ROOT_DIR)" test_tsmc_tmd_intel_pam3_hynix_tcam && "$(ROOT_DIR)/test_tsmc_tmd_intel_pam3_hynix_tcam"

.PHONY: test-ingole
test-ingole:
	$(MAKE) -C "$(ROOT_DIR)" test_ingole_wo2016199157a1 && "$(ROOT_DIR)/test_ingole_wo2016199157a1"

.PHONY: test-database
test-database:
	$(MAKE) -C "$(ROOT_DIR)" test_ternary_database && "$(ROOT_DIR)/test_ternary_database"

.PHONY: test-ai-acceleration
test-ai-acceleration:
	$(MAKE) -C "$(ROOT_DIR)" test_ai_acceleration && "$(ROOT_DIR)/test_ai_acceleration"

.PHONY: test-ft-network
test-ft-network:
	$(MAKE) -C "$(ROOT_DIR)" test_fault_tolerant_network && "$(ROOT_DIR)/test_fault_tolerant_network"

.PHONY: test-adversarial
test-adversarial:
	$(MAKE) -C "$(ROOT_DIR)" test_adversarial && "$(ROOT_DIR)/test_adversarial"

.PHONY: test-functional
test-functional:
	$(MAKE) -C "$(ROOT_DIR)" test_functional_utility && "$(ROOT_DIR)/test_functional_utility"

.PHONY: test-friday
test-friday:
	$(MAKE) -C "$(ROOT_DIR)" test_friday_updates && "$(ROOT_DIR)/test_friday_updates"

.PHONY: test-trithon
test-trithon:
	$(MAKE) -C "$(ROOT_DIR)" test-trithon

.PHONY: test-trit-linux
test-trit-linux:
	$(MAKE) -C "$(ROOT_DIR)" test-trit-linux

.PHONY: test-enhancements
test-enhancements:
	$(MAKE) -C "$(ROOT_DIR)" test-trit-enhancements

# ──────────────────────────────────────────────────────────────────────
# List all available individual targets
# ──────────────────────────────────────────────────────────────────────
.PHONY: test-individual
test-individual:
	@echo ""
	@echo "  Individual test targets (run with: make <target>)"
	@echo "  ─────────────────────────────────────────────────"
	@echo "  test-compiler          Compiler sub-suites (9)"
	@echo "  test-native            seT5 Boot (native)"
	@echo "  test-integration       Integration tests"
	@echo "  test-sel4              seL4 Ternary Moonshot"
	@echo "  test-memory            Memory safety"
	@echo "  test-scheduler         Scheduler concurrency"
	@echo "  test-tbe               TBE bootstrap"
	@echo "  test-huawei            Huawei CN119652311A HAL"
	@echo "  test-samsung-us        Samsung US11170290B2 NAND"
	@echo "  test-samsung-cn        Samsung CN105745888A modem"
	@echo "  test-tsmc-intel-hynix  TSMC/Intel/Hynix patents"
	@echo "  test-ingole            Ingole WO2016199157A1 TALU"
	@echo "  test-database          Ternary Database & Storage"
	@echo "  test-functional        Functional utility"
	@echo "  test-friday            Friday Updates (STT/IPC/TFS)"
	@echo "  test-trithon           Trithon self-test"
	@echo "  test-trit-linux        Trit Linux arch"
	@echo "  test-enhancements      Trit Linux enhancements (6)"
	@echo ""

# ──────────────────────────────────────────────────────────────────────
# Clean (delegates to root)
# ──────────────────────────────────────────────────────────────────────
.PHONY: clean
clean:
	$(MAKE) -C "$(ROOT_DIR)" clean
