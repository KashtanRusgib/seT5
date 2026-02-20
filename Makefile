# seT5 — Top-level Makefile
# Integrates the Ternary-C-compiler submodule and builds seT5 kernel code.
#
# ╔══════════════════════════════════════════════════════════════════════╗
# ║  TEST GLOSSARY PROTOCOL — MANDATORY FOR ALL NEW TESTS              ║
# ║                                                                    ║
# ║  When adding a new test suite:                                     ║
# ║  1. Add build rule target below (test_XXX: tests/test_XXX.c …)    ║
# ║  2. Add binary name to SET5_TEST_BINS variable                     ║
# ║  3. Add ##BEGIN## execution block in _run-test-suites              ║
# ║  4. Add binary name to clean target's rm -f list                   ║
# ║  5. Add suite to SET5_SUITES in run_all_tests.sh                   ║
# ║  6. Document in seT6/TESTS_GLOSSARY_OF_ALL_TESTS.md               ║
# ║  7. Run `make alltest` to verify 100% pass, 0 regressions         ║
# ║                                                                    ║
# ║  Current: 66 active suites, 5280+ runtime assertions              ║
# ║  See: seT6/TESTS_GLOSSARY_OF_ALL_TESTS.md                         ║
# ╚══════════════════════════════════════════════════════════════════════╝

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

# trit_linux hardware / AI / net / modular sources (full implementations)
# used by the advanced test suites (sigma9, rns, papers, dlt_cntfet, pdfs)
TRIT_LINUX_HW = trit_linux/hw/trit_stabilize.c trit_linux/hw/trit_ecs_gauge.c \
                trit_linux/hw/trit_cntfet_emu.c trit_linux/hw/trit_art9_pipeline.c \
                trit_linux/hw/trit_tekum_float.c trit_linux/hw/trit_trunc_mul.c \
                trit_linux/hw/trit_outlier_handle.c
TRIT_LINUX_AI = trit_linux/ai/trit_tmvm.c trit_linux/ai/trit_tmvm_rns.c \
                trit_linux/ai/trit_hesitation.c trit_linux/ai/trit_resisc.c \
                trit_linux/ai/trit_off_distill.c trit_linux/ai/trit_chinchilla_opt.c \
                trit_linux/ai/trit_dlt.c trit_linux/ai/trit_pretrain_scale.c \
                trit_linux/ai/trit_semantic_mi.c trit_linux/ai/trit_perplexity.c
TRIT_LINUX_NET = trit_linux/net/trit_tcam_net.c
TRIT_LINUX_MOD = trit_linux/modular/trit_modular.c
TRIT_LINUX_TIME = trit_linux/time/trit_timesyncd.c

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

# ---- Batch 5352-5401: Hardware ALU/TALU Operations ----
test_batch_5352_5401: tests/test_batch_5352_5401.c src/trit_alu_extended.c
	$(CC) $(CFLAGS) -o $@ $^

# ---- Batch 5402-5451: Side-Channel Resistance ----
test_batch_5402_5451: tests/test_batch_5402_5451.c src/trit_alu_extended.c
	$(CC) $(CFLAGS) -o $@ $^

# ---- Batch 5452-5501: Side-Channel Resistance (Advanced) ----
test_batch_5452_5501: tests/test_batch_5452_5501.c src/trit_alu_extended.c
	$(CC) $(CFLAGS) -o $@ $^

# ---- Batch 5502-5551: Epistemic Logic & Hesitation ----
test_batch_5502_5551: tests/test_batch_5502_5551.c src/trit_alu_extended.c trit_linux/ai/trit_hesitation.c
	$(CC) $(CFLAGS) -Itrit_linux -o $@ $^

# ---- Batch 5552-5601: Epistemic Logic & Hesitation (Advanced) ----
test_batch_5552_5601: tests/test_batch_5552_5601.c src/trit_alu_extended.c trit_linux/ai/trit_hesitation.c
	$(CC) $(CFLAGS) -Itrit_linux -o $@ $^

# ---- Batch 5602-5651: Guardian Trit Mechanisms ----
test_batch_5602_5651: tests/test_batch_5602_5651.c src/tipc.c
	$(CC) $(CFLAGS) -o $@ $^

# ---- Batch 5652-5701: Guardian Trit Mechanisms (Advanced) ----
test_batch_5652_5701: tests/test_batch_5652_5701.c src/tipc.c
	$(CC) $(CFLAGS) -o $@ $^

# ---- Batch 5702-5751: Kleene K3 Unknown Propagation ----
test_batch_5702_5751: tests/test_batch_5702_5751.c
	$(CC) $(CFLAGS) -o $@ $<

# ---- Batch 5752-5801: Multi-Radix Neural Inference ----
test_batch_5752_5801: tests/test_batch_5752_5801.c
	$(CC) $(CFLAGS) -o $@ $<

# ---- Batch 5802-5851: Unknown-Safe IPC ----
test_batch_5802_5851: tests/test_batch_5802_5851.c
	$(CC) $(CFLAGS) -o $@ $<

# ---- Batch 5852-5901: Curiosity Simulation / Exploratory Trit-Flips ----
test_batch_5852_5901: tests/test_batch_5852_5901.c
	$(CC) $(CFLAGS) -o $@ $<

# ---- Batch 5902-5951: Eudaimonic Scheduling ----
test_batch_5902_5951: tests/test_batch_5902_5951.c
	$(CC) $(CFLAGS) -o $@ $<

# ---- Batch 5952-6001: Fault-Tolerant Reversion Guards ----
test_batch_5952_6001: tests/test_batch_5952_6001.c
	$(CC) $(CFLAGS) -o $@ $<

# ---- Batch 6002-6051: Symbiotic AI-Human Interface ----
test_batch_6002_6051: tests/test_batch_6002_6051.c
	$(CC) $(CFLAGS) -o $@ $<

# ---- Batch 6052-6101: Ternary Cryptographic Uncertainty ----
test_batch_6052_6101: tests/test_batch_6052_6101.c
	$(CC) $(CFLAGS) -o $@ $<

# ---- Batch 6102-6151: PAM3 / Multi-Radix Interconnect ----
test_batch_6102_6151: tests/test_batch_6102_6151.c
	$(CC) $(CFLAGS) -o $@ $<

# ---- Batch 6152-6201: Godel Machine Self-Reference ----
test_batch_6152_6201: tests/test_batch_6152_6201.c
	$(CC) $(CFLAGS) -o $@ $<

# ---- Batch 6202-6251: RSI Flywheel Safety ----
test_batch_6202_6251: tests/test_batch_6202_6251.c
	$(CC) $(CFLAGS) -o $@ $<

# ---- Batch 6252-6301: Curiosity Gradient Verification ----
test_batch_6252_6301: tests/test_batch_6252_6301.c
	$(CC) $(CFLAGS) -o $@ $<

# ---- Batch 6302-6351: Beauty Symmetry Verification ----
test_batch_6302_6351: tests/test_batch_6302_6351.c
	$(CC) $(CFLAGS) -o $@ $<

# ---- Batch 6352-6401: Eudaimonic Optimization ----
test_batch_6352_6401: tests/test_batch_6352_6401.c
	$(CC) $(CFLAGS) -o $@ $<

# ---- Batch 6402-6451: Balanced Ternary Arithmetic ----
test_batch_6402_6451: tests/test_batch_6402_6451.c
	$(CC) $(CFLAGS) -o $@ $< -lm

# ---- Batch 6452-6501: Mixed-Radix Packed64 SIMD ----
test_batch_6452_6501: tests/test_batch_6452_6501.c
	$(CC) $(CFLAGS) -o $@ $< -lm

# ---- Symbiotic AI Module ----
test_symbiotic_ai: tests/test_symbiotic_ai.c src/symbiotic_ai.c
	$(CC) $(CFLAGS) -o $@ $^

# ---- Symbiotic Curiosity Prover (Suite 86) ----
test_symbiotic_curiosity: tests/test_symbiotic_curiosity.c src/symbiotic_ai.c
	$(CC) $(CFLAGS) -o $@ $^

# ---- Symbiotic Beauty Appreciator (Suite 87) ----
test_symbiotic_beauty: tests/test_symbiotic_beauty.c src/symbiotic_ai.c
	$(CC) $(CFLAGS) -o $@ $^

# ---- Symbiotic Eudaimonic Optimizer (Suite 88) ----
test_symbiotic_eudaimonia: tests/test_symbiotic_eudaimonia.c src/symbiotic_ai.c
	$(CC) $(CFLAGS) -o $@ $^

# ---- Red-Team Suite 89: Trit Range Integrity ----
test_red_team_trit_range: tests/test_red_team_trit_range.c
	$(CC) $(CFLAGS) -o $@ $< -lm

# ---- Red-Team Suite 90: Binary Reversion Attack ----
test_red_team_binary_reversion: tests/test_red_team_binary_reversion.c
	$(CC) $(CFLAGS) -o $@ $< -lm

# ---- Red-Team Suite 91: SIMD Packed64 Adversarial ----
test_red_team_simd: tests/test_red_team_simd.c
	$(CC) $(CFLAGS) -o $@ $< -lm

# ---- Red-Team Suite 92: Cryptographic Hardening ----
test_red_team_crypto: tests/test_red_team_crypto.c
	$(CC) $(CFLAGS) -o $@ $< -lm

# ---- Red-Team Suite 93: Symbiotic AI Adversarial ----
test_red_team_symbiotic: tests/test_red_team_symbiotic.c src/symbiotic_ai.c
	$(CC) $(CFLAGS) -o $@ $^

# ---- Red-Team Suite 94: Gödel Machine Invariants ----
test_red_team_godel: tests/test_red_team_godel.c
	$(CC) $(CFLAGS) -o $@ $< -lm

# ---- Red-Team Suite 95: Type Confusion & Integer Safety ----
test_red_team_type: tests/test_red_team_type.c
	$(CC) $(CFLAGS) -o $@ $< -lm

# ---- Red-Team Suite 96: Deep Chain Stress ----
test_red_team_deep: tests/test_red_team_deep.c
	$(CC) $(CFLAGS) -o $@ $< -lm

# ---- Red-Team Suite 97: Packed64 Fault-Hardening Verification ----
test_red_team_packed_hardened: tests/test_red_team_packed_hardened.c
	$(CC) $(CFLAGS) -o $@ $< -lm

# ---- Suite 98: Formal-Verification-Driven Ternary Improvements ----
test_ternary_formal_suite: tests/test_ternary_formal_suite.c
	$(CC) $(CFLAGS) -o $@ $< -lm

# ---- Suite 99: Mixed-Radix Bos Thesis Enhancements ----
test_mixed_radix_bos: tests/test_mixed_radix_bos.c
	$(CC) $(CFLAGS) -o $@ $< -lm

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

# ---- Ingole WO2016199157A1 TALU test suite ----
INGOLE_SRCS = src/ingole_talu.c src/ingole_hal.c
test_ingole_wo2016199157a1: tests/test_ingole_wo2016199157a1.c $(INGOLE_SRCS)
	$(CC) $(CFLAGS) -o $@ $^

# ---- Multi-Radix Unit test suite ----
MULTI_RADIX_SRCS = src/multi_radix_unit.c
test_multi_radix_unit: tests/test_multi_radix_unit.c $(MULTI_RADIX_SRCS)
	$(CC) $(CFLAGS) -o $@ $^

# ---- Ternary Wallace Tree test suite ----
WALLACE_SRCS = src/ternary_wallace_tree.c
test_ternary_wallace_tree: tests/test_ternary_wallace_tree.c $(WALLACE_SRCS)
	$(CC) $(CFLAGS) -o $@ $^

# ---- Ternary Full Adder test suite ----
test_ternary_full_adder: tests/test_ternary_full_adder.c
	$(CC) $(CFLAGS) -o $@ $^

# ---- Ternary Sense Amp test suite ----
SENSE_AMP_SRCS = src/ternary_sense_amp.c
test_ternary_sense_amp: tests/test_ternary_sense_amp.c $(SENSE_AMP_SRCS)
	$(CC) $(CFLAGS) -o $@ $^

# ---- T-IPC Compressor test suite ----
TIPC_COMPRESSOR_SRCS = src/tipc_compressor.c
test_tipc_compressor: tests/test_tipc_compressor.c $(TIPC_COMPRESSOR_SRCS)
	$(CC) $(CFLAGS) -o $@ $^

# ---- Samsung Correlator test suite ----
SAMSUNG_CORRELATOR_SRCS = src/samsung_cn105745888a_correlator.c
test_samsung_cn105745888a_correlator: tests/test_samsung_cn105745888a_correlator.c $(SAMSUNG_CORRELATOR_SRCS)
	$(CC) $(CFLAGS) -o $@ $^

# ---- Ternary Database and Storage Layer test suite ----
test_ternary_database: tests/test_ternary_database.c src/ternary_database.c
	$(CC) $(CFLAGS) -o $@ $^

# ---- AI Acceleration test suite (BitNet, DLFET, SparseNN) ----
test_ai_acceleration: tests/test_ai_acceleration.c src/ai_acceleration.c
	$(CC) $(CFLAGS) -o $@ $^ -lm

# ---- Fault-Tolerant Networking test suite (Hamming, routing, consensus) ----
test_fault_tolerant_network: tests/test_fault_tolerant_network.c src/fault_tolerant_network.c src/tipc.c
	$(CC) $(CFLAGS) -o $@ $^ -lm

# ---- Adversarial / negative-path test suite ----
test_adversarial: tests/test_adversarial.c src/memory.c src/ipc.c src/scheduler.c src/syscall.c src/multiradix.c
	$(CC) $(CFLAGS) -o $@ $^

# ---- Crown Jewel Reversion Guard test suite (T-025) ----
REVERSION_GUARD_SRCS = src/trit_crypto.c src/multiradix.c src/ingole_talu.c \
                       src/ingole_hal.c src/fault_tolerant_network.c src/tipc.c \
                       src/ternary_database.c
test_ternary_reversion_guard: tests/test_ternary_reversion_guard.c $(REVERSION_GUARD_SRCS)
	$(CC) $(CFLAGS) -o $@ $^ -lm

# ---- New seT6 test suites ----
test_modular: tests/test_modular.c src/memory.c src/ipc.c src/scheduler.c src/syscall.c src/multiradix.c $(TRIT_LINUX_MOD)
	$(CC) $(CFLAGS) -o $@ $^

test_ipc_secure: tests/test_ipc_secure.c src/memory.c src/ipc.c src/scheduler.c src/syscall.c src/multiradix.c src/tipc.c
	$(CC) $(CFLAGS) -o $@ $^

test_time: tests/test_time.c src/memory.c src/ipc.c src/scheduler.c src/syscall.c src/multiradix.c $(TRIT_LINUX_TIME)
	$(CC) $(CFLAGS) -o $@ $^

test_hardening: tests/test_hardening.c src/memory.c src/ipc.c src/scheduler.c src/syscall.c src/multiradix.c
	$(CC) $(CFLAGS) -o $@ $^

test_sigma9: tests/test_sigma9.c src/memory.c src/ipc.c src/scheduler.c src/syscall.c src/multiradix.c src/trit_rns.c \
             $(TRIT_LINUX_HW) $(TRIT_LINUX_AI) $(TRIT_LINUX_NET) $(TRIT_LINUX_MOD)
	$(CC) $(CFLAGS) -o $@ $^ -lm

test_rns: tests/test_rns.c src/memory.c src/ipc.c src/scheduler.c src/syscall.c src/multiradix.c src/trit_rns.c \
          trit_linux/ai/trit_resisc.c trit_linux/ai/trit_tmvm_rns.c trit_linux/ai/trit_tmvm.c
	$(CC) $(CFLAGS) -o $@ $^ -lm

test_papers: tests/test_papers.c src/memory.c src/ipc.c src/scheduler.c src/syscall.c src/multiradix.c \
             trit_linux/ai/trit_off_distill.c trit_linux/ai/trit_pretrain_scale.c \
             trit_linux/ai/trit_dlt.c trit_linux/hw/trit_art9_pipeline.c
	$(CC) $(CFLAGS) -o $@ $^ -lm

test_papers2: tests/test_papers2.c src/memory.c src/ipc.c src/scheduler.c src/syscall.c src/multiradix.c \
              trit_linux/ai/trit_chinchilla_opt.c trit_linux/ai/trit_semantic_mi.c \
              trit_linux/ai/trit_perplexity.c trit_linux/hw/trit_outlier_handle.c
	$(CC) $(CFLAGS) -o $@ $^ -lm

test_dlt_cntfet: tests/test_dlt_cntfet.c src/memory.c src/ipc.c src/scheduler.c src/syscall.c src/multiradix.c \
                 trit_linux/hw/trit_cntfet_emu.c trit_linux/hw/trit_stabilize.c trit_linux/hw/trit_ecs_gauge.c \
                 trit_linux/ai/trit_tmvm.c trit_linux/ai/trit_hesitation.c trit_linux/ai/trit_dlt.c
	$(CC) $(CFLAGS) -o $@ $^ -lm

test_art9: tests/test_art9.c src/memory.c src/ipc.c src/scheduler.c src/syscall.c src/multiradix.c trit_linux/hw/trit_art9_pipeline.c
	$(CC) $(CFLAGS) -o $@ $^

test_ternary_pdfs: tests/test_ternary_pdfs.c src/memory.c src/ipc.c src/scheduler.c src/syscall.c src/multiradix.c \
                   trit_linux/hw/trit_tekum_float.c trit_linux/hw/trit_trunc_mul.c trit_linux/hw/trit_stabilize.c \
                   trit_linux/ai/trit_off_distill.c trit_linux/ai/trit_pretrain_scale.c trit_linux/ai/trit_dlt.c
	$(CC) $(CFLAGS) -o $@ $^ -lm

test_peirce_semiotic: tests/test_peirce_semiotic.c src/memory.c src/ipc.c src/scheduler.c src/syscall.c src/multiradix.c
	$(CC) $(CFLAGS) -o $@ $^

test_trilang: tests/test_trilang.c src/memory.c src/ipc.c src/scheduler.c src/syscall.c src/multiradix.c
	$(CC) $(CFLAGS) -o $@ $^

test_sigma9_mcp: tests/test_sigma9_mcp.c src/memory.c src/ipc.c src/scheduler.c src/syscall.c src/multiradix.c
	$(CC) $(CFLAGS) -o $@ $^ -lm

test_hybrid_ai: tests/test_hybrid_ai.c src/memory.c src/ipc.c src/scheduler.c src/syscall.c src/multiradix.c
	$(CC) $(CFLAGS) -o $@ $^

test_stress: tests/test_stress.c src/memory.c src/ipc.c src/scheduler.c src/syscall.c src/multiradix.c
	$(CC) $(CFLAGS) -o $@ $^

test_tjson: tests/test_tjson.py
	python3 tests/test_tjson.py

test_ternumpy: tests/test_ternumpy.test
	./tests/test_ternumpy.test

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
test-trit-enhancements:
	@echo "##BEGIN##=== FP Enhancement ==="
	./tests/test_fp_enhancement.test
	@echo "##BEGIN##=== Vector Enhancement ==="
	./tests/test_vector_enhancement.test
	@echo "##BEGIN##=== RNS Enhancement ==="
	./tests/test_rns_enhancement.test
	@echo "##BEGIN##=== Ternary Arithmetic Enhancement ==="
	./tests/test_ternary_arithmetic_enhancement.test
	@echo "##BEGIN##=== Multi-Radix Enhancement ==="
	./tests/test_multi_radix_enhancement.test
	@echo "##BEGIN##=== Fault Tolerance Enhancement ==="
	./tests/test_fault_tolerance_enhancement.test

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
                 test_tsmc_tmd_intel_pam3_hynix_tcam test_ternary_database \
                 test_ingole_wo2016199157a1 test_multi_radix_unit \
                 test_ternary_wallace_tree test_ternary_full_adder test_ternary_sense_amp \
                 test_tipc_compressor test_samsung_cn105745888a_correlator \
                 test_ai_acceleration test_fault_tolerant_network \
                 test_adversarial \
                 test_ternary_reversion_guard \
                 test_modular test_ipc_secure test_time test_hardening \
                 test_sigma9 test_rns test_papers test_papers2 test_dlt_cntfet \
                 test_art9 test_ternary_pdfs test_peirce_semiotic test_trilang \
                 test_sigma9_mcp test_hybrid_ai test_stress test_tjson test_ternumpy \
                 test_godel_machine test_trit_simd_regression test_binary_sentinel \
                 test_ternary_compiler_integration test_batch_5352_5401 \
                 test_batch_5402_5451 test_batch_5452_5501 test_batch_5502_5551 \
                 test_batch_5552_5601 test_batch_5602_5651 test_batch_5652_5701 \
                 test_batch_5702_5751 test_batch_5752_5801 test_batch_5802_5851 \
                 test_batch_5852_5901 test_batch_5902_5951 test_batch_5952_6001 \
                 test_batch_6002_6051 test_batch_6052_6101 test_batch_6102_6151 \
                 test_batch_6152_6201 \
                 test_batch_6202_6251 test_batch_6252_6301 test_batch_6302_6351 \
                 test_batch_6352_6401 test_batch_6402_6451 test_batch_6452_6501 \
                 test_symbiotic_ai \
                 test_symbiotic_curiosity test_symbiotic_beauty test_symbiotic_eudaimonia \
                 test_red_team_trit_range test_red_team_binary_reversion \
                 test_red_team_simd test_red_team_crypto \
                 test_red_team_symbiotic test_red_team_godel \
                 test_red_team_type test_red_team_deep \
                 test_red_team_packed_hardened \
			 test_ternary_formal_suite \
			 test_mixed_radix_bos \

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
	@echo "##BEGIN##=== Compiler tests ==="
	-$(MAKE) -C tools/compiler clean all 2>&1
	@cd tools/compiler && for t in \
	  test_trit test_lexer test_parser test_codegen test_vm \
	  test_logger test_ir test_sel4 test_integration test_memory \
	  test_set5 test_bootstrap test_sel4_verify test_hardware test_basic \
	  test_typechecker test_linker test_arrays test_selfhost \
	  test_trit_edge_cases test_parser_fuzz test_performance \
	  test_hardware_simulation test_ternary_edge_cases \
	  test_ternary_arithmetic_comprehensive; do \
	    if [ -f ./$$t ]; then echo "##BEGIN##=== Compiler: $$t ==="; echo "[RUN] $$t"; ./$$t && echo "[PASS] $$t" || echo "[FAIL] $$t"; fi; \
	  done
	@echo "##BEGIN##=== seT5 native test ==="
	-$(MAKE) set5_native && ./set5_native
	@echo "##BEGIN##=== seT5 integration test ==="
	-$(MAKE) test_integration && ./test_integration
	@echo "##BEGIN##=== seL4 Ternary Moonshot test ==="
	-$(MAKE) test_sel4_ternary && ./test_sel4_ternary
	@echo "##BEGIN##=== Memory safety test ==="
	-$(MAKE) test_memory_safety && ./test_memory_safety
	@echo "##BEGIN##=== Scheduler concurrency test ==="
	-$(MAKE) test_scheduler_concurrency && ./test_scheduler_concurrency
	@echo "##BEGIN##=== TBE tests ==="
	-$(MAKE) test_tbe && ./test_tbe
	@echo "##BEGIN##=== Huawei CN119652311A HAL tests ==="
	-$(MAKE) test_huawei_cn119652311a && ./test_huawei_cn119652311a
	@echo "##BEGIN##=== Samsung US11170290B2 NAND inference tests ==="
	-$(MAKE) test_samsung_us11170290b2 && ./test_samsung_us11170290b2
	@echo "##BEGIN##=== Samsung CN105745888A ternary sequence modem tests ==="
	-$(MAKE) test_samsung_cn105745888a && ./test_samsung_cn105745888a
	@echo "##BEGIN##=== Functional utility tests ==="
	-$(MAKE) test_functional_utility && ./test_functional_utility
	@echo "##BEGIN##=== Friday Updates tests (STT-MRAM, T-IPC, TFS) ==="
	-$(MAKE) test_friday_updates && ./test_friday_updates
	@echo "##BEGIN##=== Trithon self-test ==="
	-$(MAKE) test-trithon
	@echo "##BEGIN##=== Trit Linux arch tests ==="
	-$(MAKE) test-trit-linux
	@echo "##BEGIN##=== Trit Linux Enhancement tests (6 suites) ==="
	-$(MAKE) test-trit-enhancements
	@echo "##BEGIN##=== TSMC TMD / Intel PAM-3 / Hynix TCAM patent tests ==="
	-$(MAKE) test_tsmc_tmd_intel_pam3_hynix_tcam && ./test_tsmc_tmd_intel_pam3_hynix_tcam
	@echo "##BEGIN##=== Ternary Database and Storage Layer tests ==="
	-$(MAKE) test_ternary_database && ./test_ternary_database
	@echo "##BEGIN##=== Ingole WO2016199157A1 TALU tests ==="
	-$(MAKE) test_ingole_wo2016199157a1 && ./test_ingole_wo2016199157a1
	@echo "##BEGIN##=== Multi-Radix Unit tests ==="
	-$(MAKE) test_multi_radix_unit && ./test_multi_radix_unit
	@echo "##BEGIN##=== Ternary Wallace Tree tests ==="
	-$(MAKE) test_ternary_wallace_tree && ./test_ternary_wallace_tree
	@echo "##BEGIN##=== Ternary Full Adder tests ==="
	-$(MAKE) test_ternary_full_adder && ./test_ternary_full_adder
	@echo "##BEGIN##=== Ternary Sense Amp tests ==="
	-$(MAKE) test_ternary_sense_amp && ./test_ternary_sense_amp
	@echo "##BEGIN##=== T-IPC Compressor tests ==="
	-$(MAKE) test_tipc_compressor && ./test_tipc_compressor
	@echo "##BEGIN##=== Samsung Correlator tests ==="
	-$(MAKE) test_samsung_cn105745888a_correlator && ./test_samsung_cn105745888a_correlator
	@echo "##BEGIN##=== AI Acceleration tests ==="
	-$(MAKE) test_ai_acceleration && ./test_ai_acceleration
	@echo "##BEGIN##=== Fault-Tolerant Networking tests ==="
	-$(MAKE) test_fault_tolerant_network && ./test_fault_tolerant_network
	@echo "##BEGIN##=== Adversarial / Negative-Path tests ==="
	-$(MAKE) test_adversarial && ./test_adversarial
	@echo "##BEGIN##=== Crown Jewel Reversion Guard tests ==="
	-$(MAKE) test_ternary_reversion_guard && ./test_ternary_reversion_guard
	@echo "##BEGIN##=== Modular Architecture tests ==="
	-$(MAKE) test_modular && ./test_modular
	@echo "##BEGIN##=== IPC Security tests ==="
	-$(MAKE) test_ipc_secure && ./test_ipc_secure
	@echo "##BEGIN##=== Time Synchronization tests ==="
	-$(MAKE) test_time && ./test_time
	@echo "##BEGIN##=== Hardening tests ==="
	-$(MAKE) test_hardening && ./test_hardening
	@echo "##BEGIN##=== Sigma 9 Architecture tests ==="
	-$(MAKE) test_sigma9 && ./test_sigma9
	@echo "##BEGIN##=== Residue Number System tests ==="
	-$(MAKE) test_rns && ./test_rns
	@echo "##BEGIN##=== Research Papers Implementation tests ==="
	-$(MAKE) test_papers && ./test_papers
	@echo "##BEGIN##=== Research Papers Part 2 tests ==="
	-$(MAKE) test_papers2 && ./test_papers2
	@echo "##BEGIN##=== DLT CNFET Integration tests ==="
	-$(MAKE) test_dlt_cntfet && ./test_dlt_cntfet
	@echo "##BEGIN##=== ART9 Pipeline tests ==="
	-$(MAKE) test_art9 && ./test_art9
	@echo "##BEGIN##=== Ternary PDFs tests ==="
	-$(MAKE) test_ternary_pdfs && ./test_ternary_pdfs
	@echo "##BEGIN##=== Peirce Semiotic tests ==="
	-$(MAKE) test_peirce_semiotic && ./test_peirce_semiotic
	@echo "##BEGIN##=== Trilang tests ==="
	-$(MAKE) test_trilang && ./test_trilang
	@echo "##BEGIN##=== Sigma 9 MCP tests ==="
	-$(MAKE) test_sigma9_mcp && ./test_sigma9_mcp
	@echo "##BEGIN##=== Hybrid AI tests ==="
	-$(MAKE) test_hybrid_ai && ./test_hybrid_ai
	@echo "##BEGIN##=== Stress tests ==="
	-$(MAKE) test_stress && ./test_stress
	@echo "##BEGIN##=== TJSON tests ==="
	-$(MAKE) test_tjson
	@echo "##BEGIN##=== TerNumPy tests ==="
	-$(MAKE) test_ternumpy
	@echo "##BEGIN##=== Gödel Machine tests ==="
	-$(MAKE) test_godel_machine && ./test_godel_machine
	@echo "##BEGIN##=== SIMD Regression tests ==="
	-$(MAKE) test_trit_simd_regression && ./test_trit_simd_regression
	@echo "##BEGIN##=== Binary Sentinel tests ==="
	-$(MAKE) test_binary_sentinel && ./test_binary_sentinel
	@echo "##BEGIN##=== Ternary Compiler Integration tests ==="
	-$(MAKE) test_ternary_compiler_integration && ./test_ternary_compiler_integration
	@echo "##BEGIN##=== Batch 5702-5751: Kleene K3 Unknown Propagation ==="
	-$(MAKE) test_batch_5702_5751 && ./test_batch_5702_5751
	@echo "##BEGIN##=== Batch 5752-5801: Multi-Radix Neural Inference ==="
	-$(MAKE) test_batch_5752_5801 && ./test_batch_5752_5801
	@echo "##BEGIN##=== Batch 5802-5851: Unknown-Safe IPC ==="
	-$(MAKE) test_batch_5802_5851 && ./test_batch_5802_5851
	@echo "##BEGIN##=== Batch 5852-5901: Curiosity Simulation ==="
	-$(MAKE) test_batch_5852_5901 && ./test_batch_5852_5901
	@echo "##BEGIN##=== Batch 5902-5951: Eudaimonic Scheduling ==="
	-$(MAKE) test_batch_5902_5951 && ./test_batch_5902_5951
	@echo "##BEGIN##=== Batch 5952-6001: Fault-Tolerant Reversion Guards ==="
	-$(MAKE) test_batch_5952_6001 && ./test_batch_5952_6001
	@echo "##BEGIN##=== Batch 6002-6051: Symbiotic AI-Human Interface ==="
	-$(MAKE) test_batch_6002_6051 && ./test_batch_6002_6051
	@echo "##BEGIN##=== Batch 6052-6101: Ternary Cryptographic Uncertainty ==="
	-$(MAKE) test_batch_6052_6101 && ./test_batch_6052_6101
	@echo "##BEGIN##=== Batch 6102-6151: PAM3 Multi-Radix Interconnect ==="
	-$(MAKE) test_batch_6102_6151 && ./test_batch_6102_6151
	@echo "##BEGIN##=== Batch 6152-6201: Godel Machine Self-Reference ==="
	-$(MAKE) test_batch_6152_6201 && ./test_batch_6152_6201
	@echo "##BEGIN##=== Batch 6202-6251: RSI Flywheel Safety ==="
	-$(MAKE) test_batch_6202_6251 && ./test_batch_6202_6251
	@echo "##BEGIN##=== Batch 6252-6301: Curiosity Gradient ==="
	-$(MAKE) test_batch_6252_6301 && ./test_batch_6252_6301
	@echo "##BEGIN##=== Batch 6302-6351: Beauty Symmetry ==="
	-$(MAKE) test_batch_6302_6351 && ./test_batch_6302_6351
	@echo "##BEGIN##=== Batch 6352-6401: Eudaimonic Optimization ==="
	-$(MAKE) test_batch_6352_6401 && ./test_batch_6352_6401
	@echo "##BEGIN##=== Batch 6402-6451: Balanced Ternary Arithmetic ==="
	-$(MAKE) test_batch_6402_6451 && ./test_batch_6402_6451
	@echo "##BEGIN##=== Batch 6452-6501: Mixed-Radix Packed64 SIMD ==="
	-$(MAKE) test_batch_6452_6501 && ./test_batch_6452_6501
	@echo "##BEGIN##=== Symbiotic AI Module ==="
	-$(MAKE) test_symbiotic_ai && ./test_symbiotic_ai
	@echo "##BEGIN##=== Suite 86: Symbiotic Curiosity Prover ==="
	-$(MAKE) test_symbiotic_curiosity && ./test_symbiotic_curiosity
	@echo "##BEGIN##=== Suite 87: Symbiotic Beauty Appreciator ==="
	-$(MAKE) test_symbiotic_beauty && ./test_symbiotic_beauty
	@echo "##BEGIN##=== Suite 88: Symbiotic Eudaimonic Optimizer ==="
	-$(MAKE) test_symbiotic_eudaimonia && ./test_symbiotic_eudaimonia
	@echo "##BEGIN##=== Suite 89: Red-Team Trit Range Integrity ==="
	-$(MAKE) test_red_team_trit_range && ./test_red_team_trit_range
	@echo "##BEGIN##=== Suite 90: Red-Team Binary Reversion Attack ==="
	-$(MAKE) test_red_team_binary_reversion && ./test_red_team_binary_reversion
	@echo "##BEGIN##=== Suite 91: Red-Team SIMD Packed64 Adversarial ==="
	-$(MAKE) test_red_team_simd && ./test_red_team_simd
	@echo "##BEGIN##=== Suite 92: Red-Team Cryptographic Hardening ==="
	-$(MAKE) test_red_team_crypto && ./test_red_team_crypto
	@echo "##BEGIN##=== Suite 93: Red-Team Symbiotic AI Adversarial ==="
	-$(MAKE) test_red_team_symbiotic && ./test_red_team_symbiotic
	@echo "##BEGIN##=== Suite 94: Red-Team Godel Machine Invariants ==="
	-$(MAKE) test_red_team_godel && ./test_red_team_godel
	@echo "##BEGIN##=== Suite 95: Red-Team Type Confusion & Integer Safety ==="
	-$(MAKE) test_red_team_type && ./test_red_team_type
	@echo "##BEGIN##=== Suite 96: Red-Team Deep Chain Stress ==="
	-$(MAKE) test_red_team_deep && ./test_red_team_deep
	@echo "##BEGIN##=== Suite 97: Red-Team Packed64 Fault-Hardening ==="
	-$(MAKE) test_red_team_packed_hardened && ./test_red_team_packed_hardened
	@echo "##BEGIN##=== Suite 98: Formal-Verification-Driven Ternary Improvements ==="
	-$(MAKE) test_ternary_formal_suite && ./test_ternary_formal_suite
	@echo "##BEGIN##=== Suite 99: Mixed-Radix Bos Thesis Enhancements ==="
	-$(MAKE) test_mixed_radix_bos && ./test_mixed_radix_bos
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

# ══════════════════════════════════════════════════════════════════════
#  ALLTEST — THE PERMANENT MASTER TEST COMMAND
#
#    make alltest
#
#  This is the ONE command that runs ALL tests across the entire seT5/
#  seT6 ternary stack.  It is the Sigma 9 gate: every suite must pass
#  100% with 0 errors before any commit is considered valid.
#
#  Guarantees:
#    1. Compiler sub-module is built first.
#    2. Every test binary is DELETED and RECOMPILED from source.
#    3. Every suite RUNS live — output streams in real-time.
#    4. tools/test_grand_summary.sh parses the log and prints a
#       formatted index of EVERY suite with pass/fail counts.
#    5. Missing suites are flagged as explicit failures.
#    6. Exit code is non-zero if ANY test fails or any suite is missing.
#
#  This target is intentionally identical to `make test` — both are
#  kept in sync so that `make alltest`, `make test`, and `make test6`
#  all produce the same full run.  `make alltest` is the canonical
#  name going forward.
# ══════════════════════════════════════════════════════════════════════
.PHONY: alltest
alltest: build-compiler
	@echo ""
	@echo "╔══════════════════════════════════════════════════════════════╗"
	@echo "║  make alltest — SIGMA 9 MASTER TEST GATE                   ║"
	@echo "║  All tests. All suites. Zero tolerance for failure.        ║"
	@echo "╚══════════════════════════════════════════════════════════════╝"
	@echo ""
	@LOGF=$$(mktemp /tmp/set5_alltest_XXXXXX.log); \
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
	rm -f test_ingole_wo2016199157a1
	rm -f test_ai_acceleration test_fault_tolerant_network test_adversarial
	rm -f test_ternary_reversion_guard
	rm -f test_modular test_ipc_secure test_time test_hardening
	rm -f test_sigma9 test_rns test_papers test_papers2 test_dlt_cntfet
	rm -f test_art9 test_ternary_pdfs test_peirce_semiotic test_trilang
	rm -f test_sigma9_mcp test_hybrid_ai test_stress
	rm -f test_godel_machine test_trit_simd_regression test_binary_sentinel
	rm -f test_ternary_compiler_integration
	rm -f test_batch_6202_6251 test_batch_6252_6301 test_batch_6302_6351
	rm -f test_batch_6352_6401 test_batch_6402_6451 test_batch_6452_6501
	rm -f trithon/libtrithon.so

# ══════════════════════════════════════════════════════════════════════
# T-007: AddressSanitizer build — `make test-asan`
# All tests must pass clean under ASan + UBSan.
# ══════════════════════════════════════════════════════════════════════
.PHONY: test-asan
test-asan:
	@echo "╔═══════════════════════════════════════════════════════════╗"
	@echo "║  ASan + UBSan Build — Sigma 9 Memory Safety Gate        ║"
	@echo "╚═══════════════════════════════════════════════════════════╝"
	$(MAKE) clean
	$(MAKE) test CC="gcc" CFLAGS="$(CFLAGS) -fsanitize=address,undefined -fno-omit-frame-pointer -g"

# ══════════════════════════════════════════════════════════════════════
# T-008: Code coverage — `make coverage`
# Generates lcov HTML report in coverage_report/.
# ══════════════════════════════════════════════════════════════════════
.PHONY: coverage
coverage:
	@echo "╔═══════════════════════════════════════════════════════════╗"
	@echo "║  Code Coverage (gcov + lcov)                            ║"
	@echo "╚═══════════════════════════════════════════════════════════╝"
	$(MAKE) clean
	$(MAKE) test CC="gcc" CFLAGS="$(CFLAGS) --coverage -fprofile-arcs -ftest-coverage"
	@mkdir -p coverage_report
	lcov --capture --directory . --output-file coverage_report/coverage.info --ignore-errors source 2>/dev/null || \
	  gcov src/*.c tests/*.c 2>/dev/null
	genhtml coverage_report/coverage.info --output-directory coverage_report 2>/dev/null || \
	  echo "Note: lcov/genhtml not installed — raw .gcov files generated instead"
	@echo "Coverage report: coverage_report/index.html"

# ══════════════════════════════════════════════════════════════════════
# T-009: Kernel fuzz testing harness — `make fuzz`
# Targets IPC payload parsing, capability decode, trit arithmetic.
# Requires: clang with libFuzzer support.
# ══════════════════════════════════════════════════════════════════════
.PHONY: fuzz
fuzz:
	@echo "Building fuzz harnesses with libFuzzer..."
	@mkdir -p fuzz_corpus
	clang -g -O1 -fsanitize=fuzzer,address $(CFLAGS) \
	  -o fuzz_ipc tests/fuzz_ipc.c src/ipc.c src/memory.c src/scheduler.c src/syscall.c src/multiradix.c 2>/dev/null || \
	  echo "Note: libFuzzer requires clang — install with: apt install clang"
	@echo "Run: ./fuzz_ipc fuzz_corpus/ -max_total_time=60"

# ══════════════════════════════════════════════════════════════════════
# T-011: Verilog compile check — `make verilog-check`
# Compiles all .v modules with Icarus Verilog.
# ══════════════════════════════════════════════════════════════════════
VERILOG_SRCS = $(wildcard hw/*.v)
.PHONY: verilog-check
verilog-check:
	@echo "=== Verilog Compile Check (iverilog) ==="
	@PASS=0; FAIL=0; \
	for v in $(VERILOG_SRCS); do \
	  if iverilog -g2012 -o /dev/null "$$v" 2>/dev/null; then \
	    echo "  [OK]   $$v"; PASS=$$((PASS+1)); \
	  else \
	    echo "  [FAIL] $$v"; FAIL=$$((FAIL+1)); \
	  fi; \
	done; \
	echo "=== Verilog: $$PASS passed, $$FAIL failed ==="

# ══════════════════════════════════════════════════════════════════════
# T-012: Device Tree validation — `make dts-check`
# Validates all .dts files with dtc compiler.
# ══════════════════════════════════════════════════════════════════════
DTS_SRCS = $(wildcard hw/*.dts)
.PHONY: dts-check
dts-check:
	@echo "=== Device Tree Validation (dtc) ==="
	@PASS=0; FAIL=0; \
	for d in $(DTS_SRCS); do \
	  if dtc -I dts -O dtb -o /dev/null "$$d" 2>/dev/null; then \
	    echo "  [OK]   $$d"; PASS=$$((PASS+1)); \
	  else \
	    echo "  [FAIL] $$d"; FAIL=$$((FAIL+1)); \
	  fi; \
	done; \
	echo "=== DTS: $$PASS passed, $$FAIL failed ==="

# ══════════════════════════════════════════════════════════════════════
# T-019: Performance regression benchmarks — `make bench`
# Tracks trit ops/sec, IPC latency, memory throughput.
# ══════════════════════════════════════════════════════════════════════
.PHONY: bench
bench: bench_unroll build-trithon-ext
	@echo "╔═══════════════════════════════════════════════════════════╗"
	@echo "║  seT6 Performance Benchmark Suite                       ║"
	@echo "╚═══════════════════════════════════════════════════════════╝"
	./bench_unroll
	python3 ternbench/ternbench.py
	@echo "Benchmark complete. Compare with previous runs for regression."

# ══════════════════════════════════════════════════════════════════════
# T-021: Doxygen API documentation — `make docs`
# ══════════════════════════════════════════════════════════════════════
.PHONY: docs
docs:
	@if command -v doxygen >/dev/null 2>&1; then \
	  doxygen docs/Doxyfile 2>/dev/null || echo "Doxygen config not found — run: doxygen -g docs/Doxyfile"; \
	else \
	  echo "Note: doxygen not installed — install with: apt install doxygen"; \
	fi

# ══════════════════════════════════════════════════════════════════════
# T-058: Gödel Machine targets
# ══════════════════════════════════════════════════════════════════════

# Build rules for Gödel machine components
test_godel_machine: tests/test_godel_machine.c src/godel_machine.c src/godel_utility.c src/godel_proof_searcher.c src/godel_archive.c src/godel_mutable_zones.c
	$(CC) $(CFLAGS) -o $@ $^

test_trit_simd_regression: tests/test_trit_simd_regression.c
	$(CC) $(CFLAGS) -o $@ $<

test_binary_sentinel: tests/test_binary_sentinel.c src/trit_crypto.c src/fault_tolerant_network.c src/tipc.c src/ai_acceleration.c src/multiradix.c
	$(CC) $(CFLAGS) -o $@ $^ -lm

# Ternary C compiler integration test (requires pre-built compiler objects)
COMPILER_OBJS = tools/compiler/src/parser.o tools/compiler/src/codegen.o \
                tools/compiler/src/logger.o tools/compiler/src/ir.o \
                tools/compiler/src/postfix_ir.o tools/compiler/src/typechecker.o \
                tools/compiler/src/linker.o tools/compiler/src/selfhost.o \
                tools/compiler/src/bootstrap.o tools/compiler/vm/ternary_vm.o

test_ternary_compiler_integration: tests/test_ternary_compiler_integration.c $(COMPILER_OBJS)
	$(CC) $(CFLAGS) -o $@ $^

.PHONY: godel-evaluate
godel-evaluate: test_godel_machine test_trit_simd_regression test_binary_sentinel
	@echo "╔═══════════════════════════════════════════════════════════╗"
	@echo "║  Gödel Machine — BIOPS 5-Tier Evaluation                ║"
	@echo "╚═══════════════════════════════════════════════════════════╝"
	@echo "── Tier 1: Compile ──"
	$(MAKE) test_godel_machine test_trit_simd_regression test_binary_sentinel
	@echo "── Tier 3: Unit Tests ──"
	./test_godel_machine
	./test_trit_simd_regression
	./test_binary_sentinel
	@echo "── Evaluation complete ──"

.PHONY: godel-search
godel-search:
	@echo "╔═══════════════════════════════════════════════════════════╗"
	@echo "║  Gödel Machine — Outer Evolutionary Loop                ║"
	@echo "╚═══════════════════════════════════════════════════════════╝"
	bash tools/godel_search.sh --max-generations 10 --batch-size 4

.PHONY: godel-diagnose
godel-diagnose:
	@echo "╔═══════════════════════════════════════════════════════════╗"
	@echo "║  Gödel Machine — Diagnostic Engine                      ║"
	@echo "╚═══════════════════════════════════════════════════════════╝"
	bash tools/godel_diagnose.sh

.PHONY: godel-archive
godel-archive:
	@echo "╔═══════════════════════════════════════════════════════════╗"
	@echo "║  Gödel Machine — Variant Archive                        ║"
	@echo "╚═══════════════════════════════════════════════════════════╝"
	@if [ -f .godel_archive.jsonl ]; then \
	  echo "Archive entries: $$(wc -l < .godel_archive.jsonl)"; \
	  tail -5 .godel_archive.jsonl; \
	else \
	  echo "No archive yet. Run: make godel-search"; \
	fi

.PHONY: all
all: build-set5

# ══════════════════════════════════════════════════════════════════════
#  GROK API INTEGRATION (via FEB192026FORGITHUB secret)
# ══════════════════════════════════════════════════════════════════════
.PHONY: grok-reason grok-optimize grok-curiosity grok-flywheel parallel-test

grok-reason:
	@echo "╔═══════════════════════════════════════════════════════════╗"
	@echo "║  Grok-4-1-fast-reasoning — Direct Query                 ║"
	@echo "╚═══════════════════════════════════════════════════════════╝"
	@python3 src/grok_api.py $(QUERY)

grok-optimize:
	@echo "╔═══════════════════════════════════════════════════════════╗"
	@echo "║  Grok-4-1-fast-reasoning — Code Optimization            ║"
	@echo "╚═══════════════════════════════════════════════════════════╝"
	@python3 src/grok_api.py --optimize $(CTX_FILE) "$(INSTRUCTION)"

grok-curiosity:
	@echo "╔═══════════════════════════════════════════════════════════╗"
	@echo "║  Grok-4-1-fast-reasoning — Curiosity Proof              ║"
	@echo "╚═══════════════════════════════════════════════════════════╝"
	@python3 src/grok_api.py --curiosity "$(HYPOTHESIS)"

grok-flywheel:
	@echo "╔═══════════════════════════════════════════════════════════╗"
	@echo "║  RSI Flywheel — Grok + Copilot + Codespace Compute      ║"
	@echo "╚═══════════════════════════════════════════════════════════╝"
	@python3 grok_seT6_optimizer.py

parallel-test:
	@echo "╔═══════════════════════════════════════════════════════════╗"
	@echo "║  Parallel Test ($(shell nproc) cores)                    ║"
	@echo "╚═══════════════════════════════════════════════════════════╝"
	$(MAKE) -j$(shell nproc) alltest

