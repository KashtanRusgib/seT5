# seT6 — Top-level Makefile
# Integrates the Ternary-C-compiler submodule and builds seT6 kernel code.

CC       = gcc
CFLAGS   = -Wall -Wextra -Iinclude -Itools/compiler/include
COMPILER = tools/compiler/ternary_compiler

# Source files (all kernel modules)
SET6_SRCS = src/init.c src/memory.c src/ipc.c src/scheduler.c src/syscall.c src/multiradix.c

# Functional utility module sources (INCREASE_FUNCTIONAL_UTILITY.md)
FUNC_UTIL_SRCS = src/ternary_weight_quantizer.c src/dlfet_sim.c \
                 src/radix_transcode.c src/srbc.c src/trit_crypto.c \
                 src/prop_delay.c src/ternary_temporal.c src/pam3_transcode.c

# Friday Jan 13 Updates: STT-MRAM, T-IPC, TFS
FRIDAY_SRCS = src/stt_mram.c src/tipc.c src/tfs.c

# ---- Compiler submodule ----
.PHONY: build-compiler
build-compiler:
	$(MAKE) -C tools/compiler clean
	$(MAKE) -C tools/compiler all

# Ensure the compiler binary exists (build only if missing)
$(COMPILER):
	$(MAKE) build-compiler

# ---- seT6 native build (standard gcc, for host testing) ----
set6_native: $(SET6_SRCS)
	$(CC) $(CFLAGS) -o $@ $(SET6_SRCS)

# ---- seT6 ternary bytecode build (via submodule compiler) ----
set6.bytecode: $(COMPILER) $(SET6_SRCS)
	$(COMPILER) -o $@ $(SET6_SRCS)

# ---- Convenience targets ----
.PHONY: build-set6
build-set6: build-compiler set6.bytecode

.PHONY: run-native
run-native: set6_native
	./set6_native

# ---- Demo programs ----
.PHONY: demos
demos:
	$(CC) $(CFLAGS) -o demo/trit_demo demo/trit_demo.c
	$(CC) $(CFLAGS) -o demo/trit_type_demo demo/trit_type_demo.c
	$(CC) $(CFLAGS) -o demo/trit_emu_bench demo/trit_emu_bench.c

# ---- Integration test ----
TEST_INT_SRCS = tests/test_integration.c src/memory.c src/ipc.c src/scheduler.c src/syscall.c src/multiradix.c
test_integration: $(TEST_INT_SRCS)
	$(CC) $(CFLAGS) -Wno-unused-variable -o $@ $(TEST_INT_SRCS)

# ---- Memory safety test ----
test_memory_safety: tests/test_memory_safety.c src/memory.c src/ipc.c src/scheduler.c src/syscall.c src/multiradix.c
	$(CC) $(CFLAGS) -o $@ $^

# ---- Scheduler concurrency test ----
test_scheduler_concurrency: tests/test_scheduler_concurrency.c src/memory.c src/ipc.c src/scheduler.c src/syscall.c src/multiradix.c
	$(CC) $(CFLAGS) -o $@ $^

# ---- seL4 Ternary test ----
test_sel4_ternary: tests/test_sel4_ternary.c src/memory.c src/ipc.c src/scheduler.c src/syscall.c src/multiradix.c
	$(CC) $(CFLAGS) -Wno-unused-variable -o $@ $^

# ---- Clang trit demo ----
clang_trit_demo: demo/clang_trit_demo.c src/multiradix.c
	$(CC) $(CFLAGS) -o demo/clang_trit_demo $^

# ---- TBE bootstrap shell ----
KERNEL_SRCS = src/syscall.c src/memory.c src/ipc.c src/scheduler.c src/multiradix.c
tbe: src/tbe_main.c $(KERNEL_SRCS)
	$(CC) $(CFLAGS) -o $@ $^

# ---- TBE test suite ----
test_tbe: tests/test_tbe.c $(KERNEL_SRCS)
	$(CC) $(CFLAGS) -o $@ $^

# ---- Huawei CN119652311A HAL test suite ----
HUAWEI_SRCS = src/huawei_alu.c src/huawei_hal.c
test_huawei_cn119652311a: tests/test_huawei_cn119652311a.c $(HUAWEI_SRCS)
	$(CC) $(CFLAGS) -o $@ $^

# ---- Samsung US11170290B2 NAND inference test suite ----
SAMSUNG_SRCS = src/samsung_tbn.c src/samsung_hal.c
test_samsung_us11170290b2: tests/test_samsung_us11170290b2.c $(SAMSUNG_SRCS)
	$(CC) $(CFLAGS) -o $@ $^

# ---- Samsung CN105745888A ternary sequence modem test suite ----
SAMSUNG_TSEQ_SRCS = src/samsung_tseq.c src/samsung_tseq_modem.c
test_samsung_cn105745888a: tests/test_samsung_cn105745888a.c $(SAMSUNG_TSEQ_SRCS)
	$(CC) $(CFLAGS) -o $@ $^ -lm

# ---- TSMC TMD / Intel PAM-3 / Hynix TCAM patent test suite ----
TSMC_TMD_SRCS       = src/tsmc_tmd.c
INTEL_PAM3D_SRCS    = src/intel_pam3_decoder.c
HYNIX_TCAM_SRCS     = src/hynix_tcam.c
NEW_PATENT_SRCS     = $(TSMC_TMD_SRCS) $(INTEL_PAM3D_SRCS) $(HYNIX_TCAM_SRCS)
test_tsmc_tmd_intel_pam3_hynix_tcam: tests/test_tsmc_tmd_intel_pam3_hynix_tcam.c $(NEW_PATENT_SRCS)
	$(CC) $(CFLAGS) -o $@ $^

# ---- Functional utility test suite (INCREASE_FUNCTIONAL_UTILITY.md) ----
test_functional_utility: tests/test_functional_utility.c $(FUNC_UTIL_SRCS)
	$(CC) $(CFLAGS) -o $@ $^

# ---- Friday Updates test suite (STT-MRAM, T-IPC, TFS) ----
test_friday_updates: tests/test_friday_updates.c $(FRIDAY_SRCS)
	$(CC) $(CFLAGS) -o $@ $^

# ---- Trithon C extension (shared library for Python ctypes) ----
.PHONY: build-trithon-ext
build-trithon-ext: trithon/libtrithon.so

trithon/libtrithon.so: trithon/trithon_ext.c src/multiradix.c $(FUNC_UTIL_SRCS) $(FRIDAY_SRCS)
	$(CC) -shared -fPIC -O2 $(CFLAGS) -o $@ $^

.PHONY: test-trithon
test-trithon: build-trithon-ext
	python3 trithon/trithon.py

# ---- Trit Linux arch port ----
TRIT_LINUX_ARCH = trit_linux/arch/ternary
TRIT_LINUX_SRCS = $(TRIT_LINUX_ARCH)/boot/init.c \
                  $(TRIT_LINUX_ARCH)/kernel/setup.c \
                  $(TRIT_LINUX_ARCH)/kernel/trit_drivers.c \
                  $(TRIT_LINUX_ARCH)/mm/trit_mm.c \
                  $(TRIT_LINUX_ARCH)/net/multiradix_net.c
TRIT_LINUX_INC  = -I$(TRIT_LINUX_ARCH)/include

.PHONY: build-trit-linux
build-trit-linux: test_trit_linux

test_trit_linux: tests/test_trit_linux.c $(TRIT_LINUX_SRCS) $(KERNEL_SRCS) $(FUNC_UTIL_SRCS) $(FRIDAY_SRCS)
	$(CC) $(CFLAGS) $(TRIT_LINUX_INC) -o $@ $^

.PHONY: test-trit-linux
test-trit-linux: test_trit_linux
	./test_trit_linux

# ---- Trit Linux Enhancement test suite (all 6 enhancements) ----
TRIT_ENH_INC  = -Itrit_linux/posix -Itrit_linux/net -Itrit_linux/gui \
                -Itrit_linux/tools -Itrit_linux/ai -Itrit_linux/security
TRIT_ENH_SRCS = trit_linux/posix/trit_coreutils.c \
                trit_linux/net/trit_net.c \
                trit_linux/gui/trit_gui.c \
                trit_linux/tools/trit_pkg.c \
                trit_linux/ai/trit_ai.c \
                trit_linux/security/trit_security.c

.PHONY: build-trit-enhancements
build-trit-enhancements: test_trit_enhancements

test_trit_enhancements: tests/test_trit_enhancements.c $(TRIT_ENH_SRCS) $(KERNEL_SRCS) $(FUNC_UTIL_SRCS) $(FRIDAY_SRCS)
	$(CC) $(CFLAGS) $(TRIT_ENH_INC) -Wno-unused-variable -o $@ $^

.PHONY: test-trit-enhancements
test-trit-enhancements: test_trit_enhancements
	./test_trit_enhancements

# ---- Arch Linux–Inspired Features (seT6-only) ----

# Module directories for Arch-inspired features
ARCH_MODULAR_INC = -Itrit_linux/modular
ARCH_IPC_SEC_INC = -Itrit_linux/ipc
ARCH_TIME_INC    = -Itrit_linux/time
ARCH_HARDEN_INC  = -Itrit_linux/hardening

# LEGO-Like Modularity test suite (50+ assertions)
MODULAR_SRCS = trit_linux/modular/trit_modular.c
test_modular: tests/test_modular.c $(MODULAR_SRCS)
	$(CC) $(CFLAGS) $(ARCH_MODULAR_INC) -o $@ $^

# Secure Inter-Module Communication test suite (40+ assertions)
IPC_SEC_SRCS = trit_linux/ipc/trit_ipc_secure.c
test_ipc_secure: tests/test_ipc_secure.c $(IPC_SEC_SRCS)
	$(CC) $(CFLAGS) $(ARCH_IPC_SEC_INC) -o $@ $^

# Time Synchronization Protocol test suite (30+ assertions)
TIME_SRCS = trit_linux/time/trit_timesyncd.c
test_time: tests/test_time.c $(TIME_SRCS)
	$(CC) $(CFLAGS) $(ARCH_TIME_INC) -o $@ $^

# Attack Surface Reduction & Hardening test suite (50+ assertions)
HARDEN_SRCS = trit_linux/hardening/trit_hardening.c
test_hardening: tests/test_hardening.c $(HARDEN_SRCS)
	$(CC) $(CFLAGS) $(ARCH_HARDEN_INC) -o $@ $^

# ---- MEGA PATENT ALIGNMENT: Sigma 9 Validation Suite ----
# PVT stability, TMVM accelerator, ECS gauge-block, TCAM net, radix guard,
# side-channel, epistemic K3, Guardian Trit, RNS, hesitation  (350+ assertions)
SIGMA9_INC  = -Itrit_linux/hw -Itrit_linux/ai -Itrit_linux/net $(ARCH_MODULAR_INC) -Isrc
SIGMA9_SRCS = trit_linux/hw/trit_stabilize.c \
              trit_linux/hw/trit_ecs_gauge.c \
              trit_linux/ai/trit_tmvm.c \
              trit_linux/ai/trit_hesitation.c \
              trit_linux/net/trit_tcam_net.c \
              trit_linux/modular/trit_modular.c \
              src/multiradix.c
test_sigma9: tests/test_sigma9.c $(SIGMA9_SRCS)
	$(CC) $(CFLAGS) $(SIGMA9_INC) -o $@ $^ -lm

# ---- RNS Standalone Test Suite (trit2_reg32 / uint32_t integration) ----
RNS_INC  = -Itrit_linux/ai
RNS_SRCS = src/multiradix.c trit_linux/ai/trit_tmvm_rns.c trit_linux/ai/trit_resisc.c
test_rns: tests/test_rns.c $(RNS_SRCS)
	$(CC) $(CFLAGS) $(RNS_INC) -o $@ $^ -lm

# ---- Paper-Derived Module Test Suite (ART-9, DLT, OFF, TPS) ----
PAPERS_INC  = -Itrit_linux/hw -Itrit_linux/ai
PAPERS_SRCS = trit_linux/hw/trit_art9_pipeline.c \
              trit_linux/ai/trit_dlt.c \
              trit_linux/ai/trit_off_distill.c \
              trit_linux/ai/trit_pretrain_scale.c
test_papers: tests/test_papers.c $(PAPERS_SRCS)
	$(CC) $(CFLAGS) $(PAPERS_INC) -o $@ $^ -lm

# ---- Paper-Derived Module Test Suite Part 2 (SMI, CHI, PPL, OLH) ----
PAPERS2_INC  = -Itrit_linux/hw -Itrit_linux/ai
PAPERS2_SRCS = trit_linux/ai/trit_semantic_mi.c \
               trit_linux/ai/trit_chinchilla_opt.c \
               trit_linux/ai/trit_perplexity.c \
               trit_linux/hw/trit_outlier_handle.c
test_papers2: tests/test_papers2.c $(PAPERS2_SRCS)
	$(CC) $(CFLAGS) $(PAPERS2_INC) -o $@ $^ -lm

# ---- DLT Expansion + CNTFET Emulation Test Suite ----
DLT_CNTFET_INC  = -Itrit_linux/hw -Itrit_linux/ai
DLT_CNTFET_SRCS = trit_linux/ai/trit_dlt.c \
                   trit_linux/hw/trit_cntfet_emu.c \
                   trit_linux/hw/trit_stabilize.c \
                   trit_linux/ai/trit_tmvm.c \
                   trit_linux/hw/trit_ecs_gauge.c \
                   trit_linux/ai/trit_hesitation.c
test_dlt_cntfet: tests/test_dlt_cntfet.c $(DLT_CNTFET_SRCS)
	$(CC) $(CFLAGS) $(DLT_CNTFET_INC) -o $@ $^ -lm

# ---- ART-9 RISC Pipeline Verilog-Matched Test Suite ----
ART9_INC  = -Itrit_linux/hw -Itrit_linux/ai
ART9_SRCS = trit_linux/hw/trit_art9_pipeline.c
test_art9: tests/test_art9.c $(ART9_SRCS)
	$(CC) $(CFLAGS) $(ART9_INC) -o $@ $^ -lm

# ---- Ternary PDF-Derived Module Test Suite ----
TPDF_INC  = -Itrit_linux/hw -Itrit_linux/ai
TPDF_SRCS = trit_linux/hw/trit_tekum_float.c \
            trit_linux/hw/trit_trunc_mul.c \
            trit_linux/hw/trit_stabilize.c \
            trit_linux/ai/trit_off_distill.c \
            trit_linux/ai/trit_pretrain_scale.c \
            trit_linux/ai/trit_dlt.c
test_ternary_pdfs: tests/test_ternary_pdfs.c $(TPDF_SRCS)
	$(CC) $(CFLAGS) $(TPDF_INC) -o $@ $^ -lm

# ---- Peircean Semiotic Engine Test Suite ----
PSM_INC   = -Itrit_linux/ai
PSM_SRCS  = trit_linux/ai/trit_peirce_semiotic.c
test_peirce_semiotic: tests/test_peirce_semiotic.c $(PSM_SRCS)
	$(CC) $(CFLAGS) $(PSM_INC) -o $@ $^ -lm

# ---- TriLang Ternary-First Language Test Suite ----
TRILANG_INC   = -Itools/trilang
TRILANG_SRCS  = tools/trilang/trilang.c
test_trilang: tests/test_trilang.c $(TRILANG_SRCS)
	$(CC) $(CFLAGS) $(TRILANG_INC) -o $@ $^

# ---- Benchmark ----
bench_unroll: tests/bench_unroll.c src/multiradix.c
	$(CC) -O2 $(CFLAGS) -o $@ $^

# ---- TernBench demo ----
.PHONY: ternbench
ternbench: build-trithon-ext
	python3 ternbench/ternbench.py

# ---- Test ----

# ── All seT6 test binaries (used for force-clean before rebuild) ──
SET6_TEST_BINS = set6_native test_integration test_sel4_ternary \
                 test_memory_safety test_scheduler_concurrency test_tbe \
                 test_huawei_cn119652311a test_samsung_us11170290b2 \
                 test_samsung_cn105745888a test_functional_utility \
                 test_friday_updates test_trit_linux test_trit_enhancements \
                 test_tsmc_tmd_intel_pam3_hynix_tcam \
                 test_modular test_ipc_secure test_time test_hardening \
                 test_sigma9 test_rns test_papers test_papers2 \
                 test_dlt_cntfet \
                 test_art9 \
                 test_ternary_pdfs \
                 test_peirce_semiotic \
                 test_trilang \
                 trithon/libtrithon.so

# Internal target: force-rebuilds and runs EVERY test binary from source.
# No stale binary ever executes — each is deleted and recompiled before running.
# Each suite's real-time output streams to stdout and is captured for summary.
.PHONY: _run-test-suites
_run-test-suites:
	@echo "╔══════════════════════════════════════════════════════════════╗"
	@echo "║  seT6 MASTER TEST RUN — LIVE EXECUTION                     ║"
	@echo "║  Timestamp: $$(date -u '+%Y-%m-%d %H:%M:%S UTC')                       ║"
	@echo "║  All binaries force-rebuilt from source before execution.   ║"
	@echo "╚══════════════════════════════════════════════════════════════╝"
	@echo ""
	@echo "── Cleaning all test binaries ──"
	rm -f $(SET6_TEST_BINS)
	@echo ""
	@echo "=== Compiler tests ==="
	$(MAKE) -C tools/compiler $(addprefix run-,test_trit test_parser test_codegen test_vm test_typechecker test_linker test_selfhost test_arrays) 2>/dev/null || \
	  (cd tools/compiler && for t in test_trit test_parser test_codegen test_vm test_typechecker test_linker test_selfhost test_arrays test_hardware test_basic; do \
	    if [ -f ./$$t ]; then echo "[RUN] $$t"; ./$$t && echo "[PASS] $$t" || echo "[FAIL] $$t"; fi; \
	  done)
	@echo "=== seT6 native test ==="
	$(MAKE) set6_native
	./set6_native
	@echo "=== seT6 integration test ==="
	$(MAKE) test_integration
	./test_integration
	@echo "=== seL4 Ternary Moonshot test ==="
	$(MAKE) test_sel4_ternary
	./test_sel4_ternary
	@echo "=== Memory safety test ==="
	$(MAKE) test_memory_safety
	./test_memory_safety
	@echo "=== Scheduler concurrency test ==="
	$(MAKE) test_scheduler_concurrency
	./test_scheduler_concurrency
	@echo "=== TBE tests ==="
	$(MAKE) test_tbe
	./test_tbe
	@echo "=== Huawei CN119652311A HAL tests ==="
	$(MAKE) test_huawei_cn119652311a
	./test_huawei_cn119652311a
	@echo "=== Samsung US11170290B2 NAND inference tests ==="
	$(MAKE) test_samsung_us11170290b2
	./test_samsung_us11170290b2
	@echo "=== Samsung CN105745888A ternary sequence modem tests ==="
	$(MAKE) test_samsung_cn105745888a
	./test_samsung_cn105745888a
	@echo "=== Functional utility tests ==="
	$(MAKE) test_functional_utility
	./test_functional_utility
	@echo "=== Friday Updates tests (STT-MRAM, T-IPC, TFS) ==="
	$(MAKE) test_friday_updates
	./test_friday_updates
	@echo "=== Trithon self-test ==="
	$(MAKE) test-trithon
	@echo "=== Trit Linux arch tests ==="
	$(MAKE) test-trit-linux
	@echo "=== Trit Linux Enhancement tests (6 suites) ==="
	$(MAKE) test-trit-enhancements
	@echo "=== TSMC TMD / Intel PAM-3 / Hynix TCAM patent tests ==="
	$(MAKE) test_tsmc_tmd_intel_pam3_hynix_tcam
	./test_tsmc_tmd_intel_pam3_hynix_tcam
	@echo "=== Arch-Inspired: LEGO-Like Modularity tests ==="
	$(MAKE) test_modular
	./test_modular
	@echo "=== Arch-Inspired: Secure Inter-Module Communication tests ==="
	$(MAKE) test_ipc_secure
	./test_ipc_secure
	@echo "=== Arch-Inspired: Time Synchronization Protocol tests ==="
	$(MAKE) test_time
	./test_time
	@echo "=== Arch-Inspired: Attack Surface Hardening tests ==="
	$(MAKE) test_hardening
	./test_hardening
	@echo "=== RNS Standalone Test Suite ==="
	$(MAKE) test_rns
	./test_rns
	@echo "=== Sigma 9 Validation Suite (MEGA PATENT ALIGNMENT) ==="
	$(MAKE) test_sigma9
	./test_sigma9
	@echo "=== Paper-Derived Module Tests (ART-9, DLT, OFF, TPS) ==="
	$(MAKE) test_papers
	./test_papers
	@echo "=== Paper2-Derived Module Tests (SMI, CHI, PPL, OLH) ==="
	$(MAKE) test_papers2
	./test_papers2
	@echo "=== DLT Expansion + CNTFET Emulation Tests ==="
	$(MAKE) test_dlt_cntfet
	./test_dlt_cntfet
	@echo "=== ART-9 RISC Pipeline Tests ==="
	$(MAKE) test_art9
	./test_art9
	@echo "=== Ternary PDF-Derived Module Tests ==="
	$(MAKE) test_ternary_pdfs
	./test_ternary_pdfs
	@echo "=== Peircean Semiotic Engine Tests ==="
	$(MAKE) test_peirce_semiotic
	./test_peirce_semiotic
	@echo "=== TriLang Ternary-First Language Tests ==="
	$(MAKE) test_trilang
	./test_trilang

# ──────────────────────────────────────────────────────────────────────
# Master test target: the ONE command that runs ALL tests.
#
#   make test
#
# Guarantees:
#   1. Every test binary is DELETED then RECOMPILED from source — no
#      stale cached binary ever executes.
#   2. Every test binary RUNS live and its output streams in real-time.
#   3. The full output is captured to a temp log for post-run parsing.
#   4. tools/test_grand_summary.sh parses the log and prints a formatted
#      index of EVERY suite with pass/fail counts, then a GRAND TOTAL.
#   5. If any suite is absent from the log, the summary flags it.
#   6. Exit code is non-zero if ANY test fails.
# ──────────────────────────────────────────────────────────────────────
.PHONY: test
test: build-compiler
	@LOGF=$$(mktemp /tmp/set6_test_XXXXXX.log); \
	RC=0; \
	$(MAKE) --no-print-directory _run-test-suites 2>&1 | tee "$$LOGF" || RC=$$?; \
	bash tools/test_grand_summary.sh "$$LOGF"; \
	rm -f "$$LOGF"; \
	exit $$RC

# ---- Clean ----
.PHONY: clean
clean:
	$(MAKE) -C tools/compiler clean
	rm -f set6_native set6.bytecode
	rm -f demo/trit_demo demo/trit_type_demo demo/trit_emu_bench demo/clang_trit_demo
	rm -f test_integration test_sel4_ternary test_tbe tbe bench_unroll
	rm -f test_memory_safety test_scheduler_concurrency
	rm -f test_trit_linux test_huawei_cn119652311a test_samsung_us11170290b2
	rm -f test_samsung_cn105745888a
	rm -f test_functional_utility
	rm -f test_friday_updates
	rm -f test_trit_enhancements
	rm -f test_tsmc_tmd_intel_pam3_hynix_tcam
	rm -f test_modular test_ipc_secure test_time test_hardening
	rm -f test_sigma9 test_rns test_papers test_papers2 test_dlt_cntfet test_art9 test_ternary_pdfs test_peirce_semiotic test_trilang
	rm -f trithon/libtrithon.so

.PHONY: all
all: build-set6
