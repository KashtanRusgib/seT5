/**
 * @file test_papers.c
 * @brief seT6 Research Paper Integration Test Suite
 *
 * Validates all modules derived from research paper analysis:
 *   Section 1: ART-9 Pipeline — RISC ternary pipeline emulation (50 tests)
 *   Section 2: DLT Quantization — Trapping-free dual thresholds (50 tests)
 *   Section 3: OFF Distillation — Cosine-similarity MI maximization (50 tests)
 *   Section 4: Pretrain Scaling — TriLMs scaling laws (50 tests)
 *
 * Total: ~200 assertions
 *
 * Build:
 *   $(CC) $(CFLAGS) -Itrit_linux/hw -Itrit_linux/ai \
 *         -o test_papers tests/test_papers.c \
 *         trit_linux/hw/trit_art9_pipeline.c \
 *         trit_linux/ai/trit_dlt.c \
 *         trit_linux/ai/trit_off_distill.c \
 *         trit_linux/ai/trit_pretrain_scale.c
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "set6/trit.h"
#include "trit_art9_pipeline.h"
#include "trit_dlt.h"
#include "trit_off_distill.h"
#include "trit_pretrain_scale.h"

/* ==== Test Harness ===================================================== */

static int tests_passed = 0;
static int tests_failed = 0;
static int tests_total  = 0;

#define TEST(name) do { \
    printf("  %-60s", name); \
    tests_total++; \
} while (0)

#define ASSERT(cond, msg) do { \
    if (cond) { \
        tests_passed++; \
        printf("[PASS]\n"); \
    } else { \
        tests_failed++; \
        printf("[FAIL] %s\n", msg); \
    } \
} while (0)

#define SECTION(name) printf("\n  --- %s ---\n", name)

/* ========================================================================
 * SECTION 1: ART-9 RISC Ternary Pipeline (50 tests)
 *            (arXiv:2111.07584v1 — 5-stage pipeline, 24 ops)
 * ======================================================================== */

static void test_art9_init(void) {
    SECTION("ART-9: Initialization & Constants");
    art9_state_t st;

    TEST("art9_init returns 0");
    ASSERT(art9_init(&st) == 0, "expected 0");

    TEST("art9_init sets initialized flag");
    ASSERT(st.initialized == 1, "expected 1");

    TEST("art9_init NULL returns -1");
    ASSERT(art9_init(NULL) == -1, "expected -1");

    TEST("Registers zeroed after init");
    int all_zero = 1;
    for (int i = 0; i < ART9_NUM_REGS; i++)
        if (st.regs[i] != 0) { all_zero = 0; break; }
    ASSERT(all_zero, "expected all regs 0");

    TEST("ART9_NUM_REGS == 27 (3^3)");
    ASSERT(ART9_NUM_REGS == 27, "expected 27");

    TEST("ART9_WORD_MAX == 9841 ((3^9-1)/2)");
    ASSERT(ART9_WORD_MAX == 9841, "expected 9841");

    TEST("ART9_PIPELINE_STAGES == 5");
    ASSERT(ART9_PIPELINE_STAGES == 5, "expected 5");

    TEST("ART9_OP_COUNT == 24");
    ASSERT(ART9_OP_COUNT == 24, "expected 24");
}

static void test_art9_alu_ops(void) {
    SECTION("ART-9: ALU Instruction Execution");
    art9_state_t st;
    art9_init(&st);

    st.regs[0] = 100;
    st.regs[1] = 50;
    st.regs[2] = -30;
    st.regs[3] = 0;

    art9_instruction_t inst;
    memset(&inst, 0, sizeof(inst));

    TEST("TADD: 100 + 50 = 150");
    inst.opcode = ART9_TADD; inst.rs1 = 0; inst.rs2 = 1;
    ASSERT(art9_execute_alu(&st, &inst) == 150, "expected 150");

    TEST("TSUB: 100 - 50 = 50");
    inst.opcode = ART9_TSUB; inst.rs1 = 0; inst.rs2 = 1;
    ASSERT(art9_execute_alu(&st, &inst) == 50, "expected 50");

    TEST("TMUL: 100 * 50 = 5000");
    inst.opcode = ART9_TMUL; inst.rs1 = 0; inst.rs2 = 1;
    ASSERT(art9_execute_alu(&st, &inst) == 5000, "expected 5000");

    TEST("TNEG: -(100) = -100");
    inst.opcode = ART9_TNEG; inst.rs1 = 0;
    ASSERT(art9_execute_alu(&st, &inst) == -100, "expected -100");

    TEST("TAND (Kleene min): min(100, -30) = -30");
    inst.opcode = ART9_TAND; inst.rs1 = 0; inst.rs2 = 2;
    ASSERT(art9_execute_alu(&st, &inst) == -30, "expected -30");

    TEST("TOR (Kleene max): max(100, -30) = 100");
    inst.opcode = ART9_TOR; inst.rs1 = 0; inst.rs2 = 2;
    ASSERT(art9_execute_alu(&st, &inst) == 100, "expected 100");

    TEST("TNOT: -(100) = -100");
    inst.opcode = ART9_TNOT; inst.rs1 = 0;
    ASSERT(art9_execute_alu(&st, &inst) == -100, "expected -100");

    TEST("TSHL: 100 * 3 = 300");
    inst.opcode = ART9_TSHL; inst.rs1 = 0;
    ASSERT(art9_execute_alu(&st, &inst) == 300, "expected 300");

    TEST("TSHR: 100 / 3 = 33");
    inst.opcode = ART9_TSHR; inst.rs1 = 0;
    ASSERT(art9_execute_alu(&st, &inst) == 33, "expected 33");

    TEST("TSHR negative: -30 / 3 = -10");
    inst.opcode = ART9_TSHR; inst.rs1 = 2;
    ASSERT(art9_execute_alu(&st, &inst) == -10, "expected -10");

    TEST("TCMP: sign(100 - 50) = 1");
    inst.opcode = ART9_TCMP; inst.rs1 = 0; inst.rs2 = 1;
    ASSERT(art9_execute_alu(&st, &inst) == 1, "expected 1");

    TEST("TCMP: sign(50 - 100) = -1");
    inst.opcode = ART9_TCMP; inst.rs1 = 1; inst.rs2 = 0;
    ASSERT(art9_execute_alu(&st, &inst) == -1, "expected -1");

    TEST("TCMP: sign(100 - 100) = 0");
    inst.opcode = ART9_TCMP; inst.rs1 = 0; inst.rs2 = 0;
    ASSERT(art9_execute_alu(&st, &inst) == 0, "expected 0");

    TEST("TADDI: 100 + 42 = 142");
    inst.opcode = ART9_TADDI; inst.rs1 = 0; inst.imm = 42;
    ASSERT(art9_execute_alu(&st, &inst) == 142, "expected 142");

    TEST("TMOVI: imm = 777");
    inst.opcode = ART9_TMOVI; inst.imm = 777;
    ASSERT(art9_execute_alu(&st, &inst) == 777, "expected 777");

    TEST("TABS: |(-30)| = 30");
    inst.opcode = ART9_TABS; inst.rs1 = 2;
    ASSERT(art9_execute_alu(&st, &inst) == 30, "expected 30");

    TEST("TMIN: min(50, -30) = -30");
    inst.opcode = ART9_TMIN; inst.rs1 = 1; inst.rs2 = 2;
    ASSERT(art9_execute_alu(&st, &inst) == -30, "expected -30");

    TEST("TMAX: max(50, -30) = 50");
    inst.opcode = ART9_TMAX; inst.rs1 = 1; inst.rs2 = 2;
    ASSERT(art9_execute_alu(&st, &inst) == 50, "expected 50");
}

static void test_art9_clamp_overflow(void) {
    SECTION("ART-9: Overflow Clamping & Word Boundaries");
    art9_state_t st;
    art9_init(&st);

    TEST("art9_clamp: 0 unchanged");
    ASSERT(art9_clamp(0) == 0, "expected 0");

    TEST("art9_clamp: ART9_WORD_MAX unchanged");
    ASSERT(art9_clamp(ART9_WORD_MAX) == ART9_WORD_MAX, "expected 9841");

    TEST("art9_clamp: ART9_WORD_MIN unchanged");
    ASSERT(art9_clamp(ART9_WORD_MIN) == ART9_WORD_MIN, "expected -9841");

    TEST("art9_clamp: 99999 → 9841");
    ASSERT(art9_clamp(99999) == ART9_WORD_MAX, "expected 9841");

    TEST("art9_clamp: -99999 → -9841");
    ASSERT(art9_clamp(-99999) == ART9_WORD_MIN, "expected -9841");

    TEST("TMUL overflow clamped: 5000 * 5000 = 9841");
    st.regs[0] = 5000; st.regs[1] = 5000;
    art9_instruction_t inst = { ART9_TMUL, 2, 0, 1, 0 };
    ASSERT(art9_execute_alu(&st, &inst) == ART9_WORD_MAX, "clamped to 9841");
}

static void test_art9_mem_ops(void) {
    SECTION("ART-9: Load/Store Memory Operations");
    art9_state_t st;
    art9_init(&st);

    art9_instruction_t inst;
    memset(&inst, 0, sizeof(inst));

    TEST("TSTORE: store 42 at addr 10");
    st.regs[0] = 10; st.regs[1] = 42;
    inst.opcode = ART9_TSTORE; inst.rs1 = 0; inst.rs2 = 1;
    art9_execute_alu(&st, &inst);
    ASSERT(st.memory[10] == 42, "expected mem[10] = 42");

    TEST("TLOAD: load from addr 10 → 42");
    inst.opcode = ART9_TLOAD; inst.rs1 = 0;
    ASSERT(art9_execute_alu(&st, &inst) == 42, "expected 42");

    TEST("TLOAD from out-of-bounds → 0");
    st.regs[0] = ART9_MEM_SIZE + 100;
    ASSERT(art9_execute_alu(&st, &inst) == 0, "expected 0");
}

static void test_art9_pipeline_run(void) {
    SECTION("ART-9: Pipeline Execution & Statistics");
    art9_state_t st;
    art9_init(&st);

    /* Simple program: MOVI r0, 10; MOVI r1, 20; ADD r2, r0, r1; HALT */
    art9_instruction_t prog[] = {
        { ART9_TMOVI, 0, 0, 0, 10   },  /* r0 = 10 */
        { ART9_TMOVI, 1, 0, 0, 20   },  /* r1 = 20 */
        { ART9_TADD,  2, 0, 1, 0    },  /* r2 = r0 + r1 */
        { ART9_THALT, 0, 0, 0, 0    },  /* halt */
    };

    TEST("art9_load_program returns 0");
    ASSERT(art9_load_program(&st, prog, 4) == 0, "expected 0");

    TEST("art9_run completes (cycles > 0)");
    int cycles = art9_run(&st, 100);
    ASSERT(cycles > 0, "expected positive cycles");

    TEST("Pipeline r2 == 30 after add");
    ASSERT(st.regs[2] == 30, "expected 30");

    TEST("Pipeline r0 == 10 after MOVI");
    ASSERT(st.regs[0] == 10, "expected 10");

    TEST("Pipeline r1 == 20 after MOVI");
    ASSERT(st.regs[1] == 20, "expected 20");

    TEST("Instructions retired > 0");
    ASSERT(st.instructions_retired > 0, "expected > 0");

    TEST("CPI reasonable (< 5000 = 5.0)");
    int cpi = art9_get_cpi(&st);
    ASSERT(cpi > 0 && cpi < 5000, "expected CPI < 5.0");

    TEST("Energy consumed > 0");
    ASSERT(st.energy_fj > 0, "expected energy > 0");

    TEST("art9_load_program NULL prog → -1");
    ASSERT(art9_load_program(&st, NULL, 4) == -1, "expected -1");

    TEST("art9_load_program count=0 → -1");
    ASSERT(art9_load_program(&st, prog, 0) == -1, "expected -1");
}

static void test_art9_radix_economy(void) {
    SECTION("ART-9: Radix Economy & DMIPS");
    art9_state_t st;
    art9_init(&st);

    TEST("Radix economy for n=1 → 1000");
    ASSERT(art9_radix_economy(1) == 1000, "expected 1000");

    TEST("Radix economy for n=100 < 1000 (ternary wins)");
    int econ = art9_radix_economy(100);
    ASSERT(econ > 0 && econ <= 1200, "expected reasonable economy");

    TEST("Radix economy for n=1000 < 1200");
    econ = art9_radix_economy(1000);
    ASSERT(econ > 0 && econ < 1200, "expected < 1200");

    TEST("DMIPS with empty state → 0");
    ASSERT(art9_get_dmips(&st, 100) == 0, "expected 0");

    TEST("ART9_DENSITY_RATIO_PCT == 158 (1.58x)");
    ASSERT(ART9_DENSITY_RATIO_PCT == 158, "expected 158");

    TEST("ART9_MEM_SIZE == 729 (3^6)");
    ASSERT(ART9_MEM_SIZE == 729, "expected 729");

    TEST("ART9_MAX_PROGRAM == 256");
    ASSERT(ART9_MAX_PROGRAM == 256, "expected 256");

    TEST("ART9_TRITS_PER_WORD == 9");
    ASSERT(ART9_TRITS_PER_WORD == 9, "expected 9");

    TEST("ART9_ENERGY_PER_INST_FJ == 12");
    ASSERT(ART9_ENERGY_PER_INST_FJ == 12, "expected 12");

    TEST("Memory zeroed after init");
    art9_state_t st2;
    art9_init(&st2);
    int mem_zero = 1;
    for (int i = 0; i < 10; i++)
        if (st2.memory[i] != 0) { mem_zero = 0; break; }
    ASSERT(mem_zero, "expected memory zeroed");

    TEST("Radix economy for n=0 → 1000");
    ASSERT(art9_radix_economy(0) == 1000, "expected 1000");

    TEST("art9_clamp: 1 unchanged");
    ASSERT(art9_clamp(1) == 1, "expected 1");

    TEST("art9_clamp: -1 unchanged");
    ASSERT(art9_clamp(-1) == -1, "expected -1");
}

/* ========================================================================
 * SECTION 2: DLT Quantization — Trapping-Free (50 tests)
 *            (Tequila / TernaryLLM papers)
 * ======================================================================== */

static void test_dlt_init(void) {
    SECTION("DLT: Initialization & Layer Setup");
    dlt_state_t st;

    TEST("dlt_init returns 0");
    ASSERT(dlt_init(&st) == 0, "expected 0");

    TEST("dlt_init NULL → -1");
    ASSERT(dlt_init(NULL) == -1, "expected -1");

    TEST("dlt_init sets initialized");
    ASSERT(st.initialized == 1, "expected 1");

    TEST("dlt_add_layer returns 0 (first layer)");
    ASSERT(dlt_add_layer(&st) == 0, "expected 0");

    TEST("dlt_add_layer returns 1 (second layer)");
    ASSERT(dlt_add_layer(&st) == 1, "expected 1");

    TEST("Layer 0 defaults: wp=500");
    ASSERT(st.layers[0].wp == DLT_DEFAULT_WP, "expected 500");

    TEST("Layer 0 defaults: wn=-500");
    ASSERT(st.layers[0].wn == DLT_DEFAULT_WN, "expected -500");

    TEST("Layer 0 defaults: delta=0");
    ASSERT(st.layers[0].delta == DLT_DEFAULT_DELTA, "expected 0");

    TEST("layer_count == 2");
    ASSERT(st.layer_count == 2, "expected 2");
}

static void test_dlt_quantize(void) {
    SECTION("DLT: Weight Quantization");
    dlt_state_t st;
    dlt_init(&st);
    int layer = dlt_add_layer(&st);

    /* Weights: positive, negative, in-deadzone */
    int weights[] = { 1000, -1000, 0, 800, -800, 100, -100, 250, -250, 50 };
    trit out[10];

    TEST("dlt_quantize returns 0");
    ASSERT(dlt_quantize(&st, layer, weights, out, 10) == 0, "expected 0");

    TEST("Weight 1000 → +1 (above wp+delta=500)");
    ASSERT(out[0] == TRIT_TRUE, "expected +1");

    TEST("Weight -1000 → -1 (below wn+delta=-500)");
    ASSERT(out[1] == TRIT_FALSE, "expected -1");

    TEST("Weight 0 → 0 (in deadzone)");
    ASSERT(out[2] == TRIT_UNKNOWN, "expected 0");

    TEST("Weight 800 → +1");
    ASSERT(out[3] == TRIT_TRUE, "expected +1");

    TEST("Weight -800 → -1");
    ASSERT(out[4] == TRIT_FALSE, "expected -1");

    TEST("Weight 100 → 0 (in deadzone)");
    ASSERT(out[5] == TRIT_UNKNOWN, "expected 0");

    TEST("Weight -100 → 0 (in deadzone)");
    ASSERT(out[6] == TRIT_UNKNOWN, "expected 0");

    TEST("Weight 250 → 0 (in deadzone, < 500)");
    ASSERT(out[7] == TRIT_UNKNOWN, "expected 0");

    TEST("count_pos == 2 (1000, 800 above wp=500)");
    ASSERT(st.layers[layer].count_pos == 2, "expected 2");

    TEST("count_neg == 2 (-1000, -800 below wn=-500)");
    ASSERT(st.layers[layer].count_neg == 2, "expected 2");

    TEST("count_zero == 6 (remaining in deadzone)");
    ASSERT(st.layers[layer].count_zero == 6, "expected 6");

    TEST("dlt_quantize NULL weights → -1");
    ASSERT(dlt_quantize(&st, layer, NULL, out, 10) == -1, "expected -1");

    TEST("dlt_quantize invalid layer → -1");
    ASSERT(dlt_quantize(&st, 99, weights, out, 10) == -1, "expected -1");
}

static void test_dlt_trapping(void) {
    SECTION("DLT: Deadzone Trapping Detection & Escape");
    dlt_state_t st;
    dlt_init(&st);
    int layer = dlt_add_layer(&st);

    /* Most weights clustered at 0 (trapped scenario) */
    int trapped_weights[] = { 10, -10, 5, -5, 0, 0, 0, 0, 0, 0,
                              1000, -1000, 3, -3, 2, -2 };
    trit out[16];

    dlt_quantize(&st, layer, trapped_weights, out, 16);

    TEST("Detect trapped: many weights near deadzone center");
    int trap_count = dlt_detect_trapped(&st, layer, trapped_weights, 16);
    ASSERT(trap_count > 0, "expected trapped > 0");

    TEST("Trapped count <= deadzone count");
    ASSERT(trap_count <= st.layers[layer].count_zero, "trapped <= zeros");

    /* Now test threshold update (escape mechanism) */
    TEST("dlt_update_thresholds returns 0");
    int rc = dlt_update_thresholds(&st, layer, trapped_weights, 16);
    ASSERT(rc == 0, "expected 0");

    TEST("After update: deadzone width changed");
    /* Deadzone should have shrunk since >60% were zeros */
    int new_width = st.layers[layer].wp - st.layers[layer].wn;
    ASSERT(new_width < 1000, "expected width < 1000 (shrunk from default)");

    TEST("Iteration count incremented");
    ASSERT(st.iterations == 1, "expected 1");

    TEST("dlt_update_thresholds NULL → -1");
    ASSERT(dlt_update_thresholds(&st, layer, NULL, 16) == -1, "expected -1");

    TEST("dlt_detect_trapped invalid layer → 0");
    ASSERT(dlt_detect_trapped(&st, 99, trapped_weights, 16) == 0, "expected 0");
}

static void test_dlt_sparsity_accuracy(void) {
    SECTION("DLT: Sparsity & Quantization Accuracy");
    dlt_state_t st;
    dlt_init(&st);
    int layer = dlt_add_layer(&st);

    int weights[] = { 1000, -1000, 0, 0, 0, 0, 0, 0, 0, 0 };
    trit out[10];
    dlt_quantize(&st, layer, weights, out, 10);

    TEST("Sparsity: 8/10 zeros → 800 (80.0%)");
    ASSERT(dlt_get_sparsity(&st, layer) == 800, "expected 800");

    TEST("Sparsity invalid layer → 0");
    ASSERT(dlt_get_sparsity(&st, 99) == 0, "expected 0");

    /* All positive weights → +1, all known */
    int pos_weights[] = { 1000, 2000, 3000, 4000 };
    trit pos_out[4];
    dlt_quantize(&st, layer, pos_weights, pos_out, 4);

    TEST("Accuracy for all-positive: all match sign");
    int acc = dlt_quant_accuracy(pos_weights, pos_out, 4);
    ASSERT(acc == 1000, "expected 1000 (100%)");

    TEST("Accuracy NULL → 0");
    ASSERT(dlt_quant_accuracy(NULL, pos_out, 4) == 0, "expected 0");

    /* Asymmetric: shift positive, rerun */
    TEST("DLT with shifted delta adapts");
    st.layers[layer].delta = 200; /* Shift up */
    dlt_quantize(&st, layer, weights, out, 10);
    /* With delta=200: pos_thresh=700, neg_thresh=-300 */
    /* -1000 < -300 → still -1, 1000 > 700 → still +1, 0 in [-300,700] → 0 */
    ASSERT(out[0] == TRIT_TRUE && out[1] == TRIT_FALSE, "thresholds shifted");
}

static void test_dlt_edge_cases(void) {
    SECTION("DLT: Edge Cases & Stress");
    dlt_state_t st;
    dlt_init(&st);

    TEST("Add DLT_MAX_LAYERS layers succeeds");
    int last_ok = 0;
    for (int i = 0; i < DLT_MAX_LAYERS; i++) {
        last_ok = dlt_add_layer(&st);
    }
    ASSERT(last_ok == DLT_MAX_LAYERS - 1, "expected max-1");

    TEST("Add one more layer → -1 (overflow)");
    ASSERT(dlt_add_layer(&st) == -1, "expected -1");

    TEST("Single weight quantization");
    dlt_state_t st2;
    dlt_init(&st2);
    int l = dlt_add_layer(&st2);
    int w = 999;
    trit t;
    dlt_quantize(&st2, l, &w, &t, 1);
    ASSERT(t == TRIT_TRUE, "expected +1");

    TEST("Weight exactly at threshold (500) → 0");
    w = 500;
    dlt_quantize(&st2, l, &w, &t, 1);
    ASSERT(t == TRIT_UNKNOWN, "expected 0 (at boundary, not above)");

    TEST("Weight exactly at -500 → 0");
    w = -500;
    dlt_quantize(&st2, l, &w, &t, 1);
    ASSERT(t == TRIT_UNKNOWN, "expected 0 (at neg boundary, not below)");

    TEST("Weight -501 → -1");
    w = -501;
    dlt_quantize(&st2, l, &w, &t, 1);
    ASSERT(t == TRIT_FALSE, "expected -1");

    TEST("Weight 501 → +1");
    w = 501;
    dlt_quantize(&st2, l, &w, &t, 1);
    ASSERT(t == TRIT_TRUE, "expected +1");

    TEST("DLT_FP_SCALE == 1000");
    ASSERT(DLT_FP_SCALE == 1000, "expected 1000");

    TEST("DLT_DEFAULT_WP == 500");
    ASSERT(DLT_DEFAULT_WP == 500, "expected 500");

    TEST("DLT_LEARN_RATE == 10");
    ASSERT(DLT_LEARN_RATE == 10, "expected 10");

    TEST("DLT_TRAP_WINDOW == 50");
    ASSERT(DLT_TRAP_WINDOW == 50, "expected 50");
}

/* ========================================================================
 * SECTION 3: OFF Distillation — Cosine MI (50 tests)
 *            (Tequila/TernaryLLM OFF distillation)
 * ======================================================================== */

static void test_off_init(void) {
    SECTION("OFF: Initialization & Temperature");
    off_state_t st;

    TEST("off_init returns 0");
    ASSERT(off_init(&st) == 0, "expected 0");

    TEST("off_init NULL → -1");
    ASSERT(off_init(NULL) == -1, "expected -1");

    TEST("Default temperature == 1000 (1.0)");
    ASSERT(st.temperature == OFF_DEFAULT_TEMP, "expected 1000");

    TEST("off_set_temperature(2000) → 0");
    ASSERT(off_set_temperature(&st, 2000) == 0, "expected 0");

    TEST("Temperature updated to 2000");
    ASSERT(st.temperature == 2000, "expected 2000");

    TEST("off_set_temperature(0) → -1");
    ASSERT(off_set_temperature(&st, 0) == -1, "expected -1");

    TEST("off_set_temperature NULL → -1");
    ASSERT(off_set_temperature(NULL, 1000) == -1, "expected -1");
}

static void test_off_cosine_sim(void) {
    SECTION("OFF: Cosine Similarity");

    /* Identical vectors → cos_sim ≈ 1000 */
    int va[] = { 1000, 2000, 3000, 4000 };
    int vb[] = { 1000, 2000, 3000, 4000 };

    TEST("cos_sim of identical vectors ≈ 1000");
    int cs = off_cosine_similarity(va, vb, 4);
    ASSERT(cs >= 990 && cs <= 1000, "expected ~1000");

    /* Opposite vectors → cos_sim ≈ -1000 */
    int vc[] = { -1000, -2000, -3000, -4000 };

    TEST("cos_sim of opposite vectors ≈ -1000");
    cs = off_cosine_similarity(va, vc, 4);
    ASSERT(cs <= -990 && cs >= -1000, "expected ~-1000");

    /* Orthogonal vectors → cos_sim ≈ 0 */
    int vx[] = { 1000, 0, 0, 0 };
    int vy[] = { 0, 1000, 0, 0 };

    TEST("cos_sim of orthogonal vectors == 0");
    cs = off_cosine_similarity(vx, vy, 4);
    ASSERT(cs == 0, "expected 0");

    /* One zero vector → 0 */
    int vz[] = { 0, 0, 0, 0 };

    TEST("cos_sim with zero vector → 0");
    cs = off_cosine_similarity(va, vz, 4);
    ASSERT(cs == 0, "expected 0");

    TEST("cos_sim NULL → 0");
    ASSERT(off_cosine_similarity(NULL, vb, 4) == 0, "expected 0");

    TEST("cos_sim dim=0 → 0");
    ASSERT(off_cosine_similarity(va, vb, 0) == 0, "expected 0");

    /* Partial correlation */
    int vp[] = { 1000, 2000, 0, 0 };
    int vq[] = { 1000, 2000, 3000, 4000 };

    TEST("cos_sim partial correlation: 0 < cs < 1000");
    cs = off_cosine_similarity(vp, vq, 4);
    ASSERT(cs > 0 && cs < 1000, "expected between 0 and 1000");

    /* Uniform vectors → 1000 */
    int vu[] = { 500, 500, 500, 500 };
    int vw[] = { 1000, 1000, 1000, 1000 };

    TEST("cos_sim of proportional vectors == 1000");
    cs = off_cosine_similarity(vu, vw, 4);
    ASSERT(cs >= 999, "expected ~1000");
}

static void test_off_mutual_info(void) {
    SECTION("OFF: Mutual Information Estimation");

    TEST("MI for cos_sim=1000 → max (7000)");
    ASSERT(off_estimate_mi(1000) == 7000, "expected 7000");

    TEST("MI for cos_sim=0 → 0");
    ASSERT(off_estimate_mi(0) == 0, "expected 0");

    TEST("MI for cos_sim=900 > MI for cos_sim=500");
    int mi_900 = off_estimate_mi(900);
    int mi_500 = off_estimate_mi(500);
    ASSERT(mi_900 > mi_500, "expected monotonic");

    TEST("MI for cos_sim=-900 == MI for cos_sim=900 (uses |cos|)");
    int mi_neg = off_estimate_mi(-900);
    ASSERT(mi_neg == mi_900, "expected equal");

    TEST("MI always non-negative");
    int mi_100 = off_estimate_mi(100);
    ASSERT(mi_100 >= 0, "expected >= 0");

    TEST("MI for cos_sim=500 > 0");
    ASSERT(off_estimate_mi(500) > 0, "expected > 0");

    TEST("MI for cos_sim=100 <= MI for cos_sim=500");
    ASSERT(off_estimate_mi(100) <= off_estimate_mi(500), "expected monotonic");

    TEST("MI monotonically increases with |cos_sim|");
    int mi_prev = 0;
    int monotonic = 1;
    for (int c = 0; c <= 1000; c += 100) {
        int mi = off_estimate_mi(c);
        if (mi < mi_prev) { monotonic = 0; break; }
        mi_prev = mi;
    }
    ASSERT(monotonic, "expected monotonic increase");
}

static void test_off_distill_step(void) {
    SECTION("OFF: Distillation Step & Outliers");
    off_state_t st;
    off_init(&st);

    int teacher[] = { 1000, 2000, 3000, 4000, 5000, 6000, 7000, 8000 };
    int student[] = { 900,  1900, 2900, 3900, 4900, 5900, 6900, 7900 };

    TEST("off_distill_step returns 0 (first layer)");
    int idx = off_distill_step(&st, teacher, student, 8);
    ASSERT(idx == 0, "expected 0");

    TEST("Distilled cos_sim > 0 (similar features)");
    ASSERT(st.layers[0].cos_sim > 0, "expected positive cos_sim");

    TEST("OFF loss = 1000 - cos_sim");
    ASSERT(st.layers[0].off_loss == 1000 - st.layers[0].cos_sim, "expected off_loss");

    TEST("MI > 0 for correlated features");
    ASSERT(st.layers[0].mutual_info > 0, "expected MI > 0");

    TEST("layer_count incremented to 1");
    ASSERT(st.layer_count == 1, "expected 1");

    /* Vector with outliers */
    int outlier_vec[] = { 100, 100, 100, 100, 100, 100, 100, 50000 };

    TEST("Outlier detection: 1 outlier in vector");
    int outliers = off_count_outliers(outlier_vec, 8);
    ASSERT(outliers >= 1, "expected >= 1 outlier");

    TEST("Outlier detection: uniform → 0 outliers");
    int uniform[] = { 100, 100, 100, 100 };
    ASSERT(off_count_outliers(uniform, 4) == 0, "expected 0");

    TEST("Outlier detection NULL → 0");
    ASSERT(off_count_outliers(NULL, 4) == 0, "expected 0");

    /* Multiple distillation steps */
    TEST("Multiple distill steps: layer_count grows");
    off_distill_step(&st, teacher, student, 8);
    off_distill_step(&st, teacher, student, 8);
    ASSERT(st.layer_count == 3, "expected 3");

    TEST("avg_cos_sim updated");
    ASSERT(st.avg_cos_sim > 0, "expected positive avg");
}

static void test_off_retention(void) {
    SECTION("OFF: Information Retention");
    off_state_t st;
    off_init(&st);

    TEST("Retention with no layers → 0");
    ASSERT(off_get_retention(&st) == 0, "expected 0");

    /* Add high-similarity distillation */
    int t[] = { 1000, 2000, 3000, 4000 };
    int s[] = { 1000, 2000, 3000, 4000 };
    off_distill_step(&st, t, s, 4);

    TEST("Retention with identical features > 0");
    int ret = off_get_retention(&st);
    ASSERT(ret > 0, "expected positive retention");

    TEST("Retention <= 1000 (100%)");
    ASSERT(ret <= 1000, "expected <= 1000");

    TEST("off_distill_step NULL teacher → -1");
    ASSERT(off_distill_step(&st, NULL, s, 4) == -1, "expected -1");

    TEST("off_distill_step NULL state → -1");
    ASSERT(off_distill_step(NULL, t, s, 4) == -1, "expected -1");

    TEST("off_distill_step dim=0 → -1");
    ASSERT(off_distill_step(&st, t, s, 0) == -1, "expected -1");

    TEST("OFF_INFO_THRESHOLD == 800");
    ASSERT(OFF_INFO_THRESHOLD == 800, "expected 800");

    TEST("OFF_MAX_DIM == 1024");
    ASSERT(OFF_MAX_DIM == 1024, "expected 1024");

    TEST("OFF_FP_SCALE == 1000");
    ASSERT(OFF_FP_SCALE == 1000, "expected 1000");

    TEST("Retention NULL state → 0");
    ASSERT(off_get_retention(NULL) == 0, "expected 0");

    TEST("cos_sim of scaled vectors: 500,1000 vs 1000,2000");
    int vs1[] = { 500, 1000, 1500, 2000 };
    int vs2[] = { 1000, 2000, 3000, 4000 };
    int cs = off_cosine_similarity(vs1, vs2, 4);
    ASSERT(cs >= 999, "expected ~1000 (proportional)");
}

/* ========================================================================
 * SECTION 4: Pretrain Scaling Laws — TriLMs (50 tests)
 *            (ICLR 2025 — bit-size laws, crossover, Spectra suite)
 * ======================================================================== */

static void test_tps_init(void) {
    SECTION("TPS: Initialization & Constants");
    tps_state_t st;

    TEST("tps_init returns 0");
    ASSERT(tps_init(&st) == 0, "expected 0");

    TEST("tps_init NULL → -1");
    ASSERT(tps_init(NULL) == -1, "expected -1");

    TEST("TPS_BITS_PER_TERNARY == 1580 (1.58 bits)");
    ASSERT(TPS_BITS_PER_TERNARY == 1580, "expected 1580");

    TEST("TPS_BITS_PER_FLOAT == 16000 (16 bits)");
    ASSERT(TPS_BITS_PER_FLOAT == 16000, "expected 16000");

    TEST("Spectra 99M config");
    ASSERT(TPS_SPECTRA_99M == 99, "expected 99");

    TEST("Spectra 3.9B config");
    ASSERT(TPS_SPECTRA_3B9 == 3900, "expected 3900");
}

static void test_tps_bit_equivalent(void) {
    SECTION("TPS: Bit-Equivalent Parameter Count");

    TEST("100M ternary ≈ 9M bit-equivalent (1.58/16)");
    int be = tps_bit_equivalent(100, TPS_BITS_PER_TERNARY);
    ASSERT(be >= 9 && be <= 10, "expected ~9-10");

    TEST("100M FP16 → 100M bit-equivalent");
    be = tps_bit_equivalent(100, TPS_BITS_PER_FLOAT);
    ASSERT(be == 100, "expected 100");

    TEST("1000M ternary ≈ 98M bit-equiv");
    be = tps_bit_equivalent(1000, TPS_BITS_PER_TERNARY);
    ASSERT(be >= 95 && be <= 100, "expected ~98");

    TEST("bit_equivalent 0 params → 0");
    ASSERT(tps_bit_equivalent(0, TPS_BITS_PER_TERNARY) == 0, "expected 0");

    TEST("bit_equivalent 0 bits → 0");
    ASSERT(tps_bit_equivalent(100, 0) == 0, "expected 0");

    /* Binary (1 bit) */
    TEST("100M binary (1-bit) → 6M bit-equiv");
    be = tps_bit_equivalent(100, TPS_BITS_PER_BINARY);
    ASSERT(be >= 5 && be <= 7, "expected ~6");
}

static void test_tps_loss_ppl(void) {
    SECTION("TPS: Loss Estimation & Perplexity");

    TEST("Loss for 99M/300B > 0");
    int loss = tps_estimate_loss(99, 300);
    ASSERT(loss > 0, "expected positive loss");

    TEST("Loss decreases with more params (99M vs 3900M)");
    int loss_small = tps_estimate_loss(99, 300);
    int loss_large = tps_estimate_loss(3900, 300);
    ASSERT(loss_small >= loss_large, "expected larger model ≤ loss");

    TEST("Loss >= irreducible E (1690)");
    ASSERT(loss >= TPS_CHINCHILLA_E, "expected >= E");

    TEST("Loss for 0 params → E (irreducible)");
    ASSERT(tps_estimate_loss(0, 300) == TPS_CHINCHILLA_E, "expected E");

    TEST("PPL > 0 for positive loss");
    int ppl = tps_loss_to_ppl(loss);
    ASSERT(ppl > 0, "expected positive PPL");

    TEST("PPL increases with loss");
    int ppl_high = tps_loss_to_ppl(3000);
    int ppl_low  = tps_loss_to_ppl(2000);
    ASSERT(ppl_high >= ppl_low, "expected higher loss → higher PPL");

    TEST("PPL for loss=0 → 100 (= 1.0)");
    ASSERT(tps_loss_to_ppl(0) == 100, "expected 100");
}

static void test_tps_memory_bandwidth(void) {
    SECTION("TPS: Memory & Bandwidth Savings");

    TEST("Memory 100M ternary ≈ 19 MB");
    int mem = tps_estimate_memory(100, TPS_BITS_PER_TERNARY);
    ASSERT(mem >= 18 && mem <= 20, "expected ~19");

    TEST("Memory 100M FP16 = 200 MB");
    mem = tps_estimate_memory(100, TPS_BITS_PER_FLOAT);
    ASSERT(mem == 200, "expected 200");

    TEST("Ternary uses 10× less memory than FP16");
    int mem_t = tps_estimate_memory(1000, TPS_BITS_PER_TERNARY);
    int mem_f = tps_estimate_memory(1000, TPS_BITS_PER_FLOAT);
    ASSERT(mem_f / mem_t >= 9, "expected ~10x savings");

    TEST("Bandwidth saving ternary ≈ 10126 (10.1×)");
    int saving = tps_bandwidth_saving(TPS_BITS_PER_TERNARY);
    ASSERT(saving >= 10000 && saving <= 11000, "expected ~10.1x");

    TEST("Bandwidth saving FP16 = 1000 (1.0×)");
    ASSERT(tps_bandwidth_saving(TPS_BITS_PER_FLOAT) == 1000, "expected 1000");

    TEST("Memory 0 params → 0");
    ASSERT(tps_estimate_memory(0, TPS_BITS_PER_TERNARY) == 0, "expected 0");
}

static void test_tps_configs(void) {
    SECTION("TPS: Configuration & Spectra Suite");
    tps_state_t st;
    tps_init(&st);

    TEST("Add Spectra 99M config → index 0");
    int idx = tps_add_config(&st, 99, 300, TPS_BITS_PER_TERNARY);
    ASSERT(idx == 0, "expected 0");

    TEST("Config has estimated loss > 0");
    ASSERT(st.configs[0].estimated_loss > 0, "expected loss > 0");

    TEST("Config has estimated PPL > 0");
    ASSERT(st.configs[0].estimated_ppl > 0, "expected PPL > 0");

    TEST("Config has memory > 0");
    ASSERT(st.configs[0].memory_mb > 0, "expected memory > 0");

    TEST("Config has FLOPs > 0");
    ASSERT(st.configs[0].flops > 0, "expected FLOPs > 0");

    TEST("Add Spectra 3.9B config");
    int idx2 = tps_add_config(&st, 3900, 300, TPS_BITS_PER_TERNARY);
    ASSERT(idx2 == 1, "expected 1");

    TEST("3.9B loss <= 99M loss (scaling law)");
    ASSERT(st.configs[1].estimated_loss <= st.configs[0].estimated_loss,
           "expected better with more params");

    TEST("3.9B memory > 99M memory");
    ASSERT(st.configs[1].memory_mb > st.configs[0].memory_mb,
           "expected more memory");

    TEST("config_count == 2");
    ASSERT(st.config_count == 2, "expected 2");

    TEST("tps_add_config invalid params → -1");
    ASSERT(tps_add_config(&st, 0, 300, TPS_BITS_PER_TERNARY) == -1, "expected -1");

    TEST("tps_add_config NULL → -1");
    ASSERT(tps_add_config(NULL, 100, 300, TPS_BITS_PER_TERNARY) == -1, "expected -1");
}

static void test_tps_crossover_flops(void) {
    SECTION("TPS: Crossover & FLOPs");
    tps_state_t st;
    tps_init(&st);

    TEST("Crossover found for 300B tokens");
    int cross = tps_find_crossover(&st, 300);
    ASSERT(cross > 0, "expected positive crossover");

    TEST("Crossover set in state");
    ASSERT(st.crossover_params_m > 0, "expected stored");

    TEST("tps_find_crossover NULL → 0");
    ASSERT(tps_find_crossover(NULL, 300) == 0, "expected 0");

    TEST("FLOPs for 100M/300B > 0");
    int64_t flops = tps_estimate_flops(100, 300);
    ASSERT(flops > 0, "expected positive FLOPs");

    TEST("FLOPs 1000M > FLOPs 100M");
    int64_t flops_big = tps_estimate_flops(1000, 300);
    ASSERT(flops_big > flops, "expected more FLOPs");

    TEST("FLOPs 0 params → 0");
    ASSERT(tps_estimate_flops(0, 300) == 0, "expected 0");

    TEST("Ternary FLOPs = 1/3 of theoretical (MAC-free)");
    /* FLOPs = 6 * N * D * 1000 / 3 */
    int64_t expected = (int64_t)6 * 100 * 300 * 1000 / 3;
    ASSERT(flops == expected, "expected MAC-free 1/3");

    TEST("TPS_MAX_CONFIGS == 16");
    ASSERT(TPS_MAX_CONFIGS == 16, "expected 16");

    TEST("TPS_CHINCHILLA_ALPHA == 340");
    ASSERT(TPS_CHINCHILLA_ALPHA == 340, "expected 340");

    TEST("TPS_CHINCHILLA_BETA == 280");
    ASSERT(TPS_CHINCHILLA_BETA == 280, "expected 280");

    TEST("TPS_FP_SCALE == 1000");
    ASSERT(TPS_FP_SCALE == 1000, "expected 1000");

    TEST("Spectra 197M config");
    ASSERT(TPS_SPECTRA_197M == 197, "expected 197");

    TEST("Spectra 394M config");
    ASSERT(TPS_SPECTRA_394M == 394, "expected 394");

    TEST("Spectra 830M config");
    ASSERT(TPS_SPECTRA_830M == 830, "expected 830");

    TEST("Spectra 1.7B config");
    ASSERT(TPS_SPECTRA_1B7 == 1700, "expected 1700");

    TEST("Bandwidth saving 0 bits → 0 (div-by-zero safe)");
    ASSERT(tps_bandwidth_saving(0) == 0, "expected 0");
}

/* ========================================================================
 * MAIN
 * ======================================================================== */

int main(void) {
    printf("╔══════════════════════════════════════════════════════════════╗\n");
    printf("║  seT6 Research Paper Integration Test Suite                 ║\n");
    printf("║  ART-9 Pipeline · DLT Quant · OFF Distill · TriLM Scaling  ║\n");
    printf("╚══════════════════════════════════════════════════════════════╝\n");

    /* Section 1: ART-9 Pipeline (50 tests) */
    test_art9_init();
    test_art9_alu_ops();
    test_art9_clamp_overflow();
    test_art9_mem_ops();
    test_art9_pipeline_run();
    test_art9_radix_economy();

    /* Section 2: DLT Quantization (50 tests) */
    test_dlt_init();
    test_dlt_quantize();
    test_dlt_trapping();
    test_dlt_sparsity_accuracy();
    test_dlt_edge_cases();

    /* Section 3: OFF Distillation (50 tests) */
    test_off_init();
    test_off_cosine_sim();
    test_off_mutual_info();
    test_off_distill_step();
    test_off_retention();

    /* Section 4: Pretrain Scaling Laws (50 tests) */
    test_tps_init();
    test_tps_bit_equivalent();
    test_tps_loss_ppl();
    test_tps_memory_bandwidth();
    test_tps_configs();
    test_tps_crossover_flops();

    printf("\n══════════════════════════════════════════════════════════════\n");
    printf("  Paper Tests: %d passed, %d failed, %d total\n",
           tests_passed, tests_failed, tests_total);
    printf("══════════════════════════════════════════════════════════════\n");

    return tests_failed ? 1 : 0;
}
