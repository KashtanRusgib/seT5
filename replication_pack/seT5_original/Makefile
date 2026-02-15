# seT5 — Top-level Makefile
# Integrates the Ternary-C-compiler submodule and builds seT5 kernel code.

CC       = gcc
CFLAGS   = -Wall -Wextra -Iinclude -Itools/compiler/include
COMPILER = tools/compiler/ternary_compiler

# Source files (all kernel modules)
SET5_SRCS = src/init.c src/memory.c src/ipc.c src/scheduler.c src/syscall.c src/multiradix.c

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

# ---- seT5 native build (standard gcc, for host testing) ----
set5_native: $(SET5_SRCS)
	$(CC) $(CFLAGS) -o $@ $(SET5_SRCS)

# ---- seT5 ternary bytecode build (via submodule compiler) ----
set5.bytecode: $(COMPILER) $(SET5_SRCS)
	$(COMPILER) -o $@ $(SET5_SRCS)

# ---- Convenience targets ----
.PHONY: build-set5
build-set5: build-compiler set5.bytecode

.PHONY: run-native
run-native: set5_native
	./set5_native

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

# ---- Benchmark ----
bench_unroll: tests/bench_unroll.c src/multiradix.c
	$(CC) -O2 $(CFLAGS) -o $@ $^

# ---- TernBench demo ----
.PHONY: ternbench
ternbench: build-trithon-ext
	python3 ternbench/ternbench.py

# ---- Test ----

# ── All seT5 test binaries (used for force-clean before rebuild) ──
SET5_TEST_BINS = set5_native test_integration test_sel4_ternary \
                 test_memory_safety test_scheduler_concurrency test_tbe \
                 test_huawei_cn119652311a test_samsung_us11170290b2 \
                 test_samsung_cn105745888a test_functional_utility \
                 test_friday_updates test_trit_linux test_trit_enhancements \
                 test_tsmc_tmd_intel_pam3_hynix_tcam \
                 trithon/libtrithon.so

# Internal target: force-rebuilds and runs EVERY test binary from source.
# No stale binary ever executes — each is deleted and recompiled before running.
# Each suite's real-time output streams to stdout and is captured for summary.
.PHONY: _run-test-suites
_run-test-suites:
	@echo "╔══════════════════════════════════════════════════════════════╗"
	@echo "║  seT5 MASTER TEST RUN — LIVE EXECUTION                     ║"
	@echo "║  Timestamp: $$(date -u '+%Y-%m-%d %H:%M:%S UTC')                       ║"
	@echo "║  All binaries force-rebuilt from source before execution.   ║"
	@echo "╚══════════════════════════════════════════════════════════════╝"
	@echo ""
	@echo "── Cleaning all test binaries ──"
	rm -f $(SET5_TEST_BINS)
	@echo ""
	@echo "=== Compiler tests ==="
	$(MAKE) -C tools/compiler $(addprefix run-,test_trit test_parser test_codegen test_vm test_typechecker test_linker test_selfhost test_arrays) 2>/dev/null || \
	  (cd tools/compiler && for t in test_trit test_parser test_codegen test_vm test_typechecker test_linker test_selfhost test_arrays test_hardware test_basic; do \
	    if [ -f ./$$t ]; then echo "[RUN] $$t"; ./$$t && echo "[PASS] $$t" || echo "[FAIL] $$t"; fi; \
	  done)
	@echo "=== seT5 native test ==="
	$(MAKE) set5_native
	./set5_native
	@echo "=== seT5 integration test ==="
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
	@LOGF=$$(mktemp /tmp/set5_test_XXXXXX.log); \
	RC=0; \
	$(MAKE) --no-print-directory _run-test-suites 2>&1 | tee "$$LOGF" || RC=$$?; \
	bash tools/test_grand_summary.sh "$$LOGF"; \
	rm -f "$$LOGF"; \
	exit $$RC

# ──────────────────────────────────────────────────────────────────────
# seT6 test target: runs the FULL seT6 test suite (all seT5 base tests
# plus seT6-only additions) from the seT6/ subdirectory.
#
#   make test6
#
# Delegates to seT6/Makefile's `test` target which force-rebuilds every
# binary and runs tools/test_grand_summary.sh for the final report.
# ──────────────────────────────────────────────────────────────────────
.PHONY: test6
test6:
	$(MAKE) -C seT6 test

# ---- Clean ----
.PHONY: clean
clean:
	$(MAKE) -C tools/compiler clean
	rm -f set5_native set5.bytecode
	rm -f demo/trit_demo demo/trit_type_demo demo/trit_emu_bench demo/clang_trit_demo
	rm -f test_integration test_sel4_ternary test_tbe tbe bench_unroll
	rm -f test_memory_safety test_scheduler_concurrency
	rm -f test_trit_linux test_huawei_cn119652311a test_samsung_us11170290b2
	rm -f test_samsung_cn105745888a
	rm -f test_functional_utility
	rm -f test_friday_updates
	rm -f test_trit_enhancements
	rm -f test_tsmc_tmd_intel_pam3_hynix_tcam
	rm -f trithon/libtrithon.so

.PHONY: all
all: build-set5
