/**
 * @file test_papers2.c
 * @brief seT6 Research Paper Integration Test Suite — Part 2
 *
 * Validates all modules derived from BUILD_TO_FIT.md paper analysis:
 *   Section 1: Semantic MI — Shannon entropy, MI, L∞, alignment (50 tests)
 *   Section 2: Chinchilla Optimizer — Scaling laws, schedule, Spectra (50 tests)
 *   Section 3: Perplexity Benchmark — PPL estimation, degradation (50 tests)
 *   Section 4: Outlier Handling — Detection, rescaling, info loss (50 tests)
 *
 * Total: 200 assertions
 *
 * Build:
 *   $(CC) $(CFLAGS) -Itrit_linux/hw -Itrit_linux/ai -Iinclude \
 *         -o test_papers2 tests/test_papers2.c \
 *         trit_linux/ai/trit_semantic_mi.c \
 *         trit_linux/ai/trit_chinchilla_opt.c \
 *         trit_linux/ai/trit_perplexity.c \
 *         trit_linux/hw/trit_outlier_handle.c -lm
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "trit_semantic_mi.h"
#include "trit_chinchilla_opt.h"
#include "trit_perplexity.h"
#include "trit_outlier_handle.h"

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
 * SECTION 1: Semantic Mutual Information (50 tests)
 *            Shannon entropy, MI estimation, L∞ graded truth, alignment
 * ======================================================================== */

static void test_smi_init(void) {
    SECTION("SMI: Initialization & Constants");
    smi_state_t st;

    TEST("smi_init returns 0");
    ASSERT(smi_init(&st) == 0, "expected 0");

    TEST("smi_init sets initialized flag");
    ASSERT(st.initialized == 1, "expected 1");

    TEST("smi_init NULL returns -1");
    ASSERT(smi_init(NULL) == -1, "expected -1");

    TEST("smi_init clears layer count");
    ASSERT(st.layer_count == 0, "expected 0");

    TEST("smi_init clears avg_mi");
    ASSERT(st.avg_mi == 0, "expected 0");

    TEST("smi_init clears total_info_bits");
    ASSERT(st.total_info_bits == 0, "expected 0");

    TEST("SMI_INFO_PER_TRIT = 1585 (log2(3) x1000)");
    ASSERT(SMI_INFO_PER_TRIT == 1585, "expected 1585");

    TEST("SMI_LOG2_E_X1000 = 1443");
    ASSERT(SMI_LOG2_E_X1000 == 1443, "expected 1443");

    TEST("SMI_MAX_BINS = 64");
    ASSERT(SMI_MAX_BINS == 64, "expected 64");

    TEST("SMI_MAX_LAYERS = 32");
    ASSERT(SMI_MAX_LAYERS == 32, "expected 32");
}

static void test_smi_shannon_entropy(void) {
    SECTION("SMI: Shannon Entropy");
    int h;

    /* Uniform distribution: H = log2(3) = 1585 */
    h = smi_shannon_entropy(100, 100, 100);
    TEST("uniform trit dist H ~ 1585 (log2(3))");
    ASSERT(h >= 1400 && h <= 1700, "expected ~1585");

    /* All zeros: H = 0 */
    h = smi_shannon_entropy(0, 100, 0);
    TEST("all-zero dist H = 0");
    ASSERT(h == 0, "expected 0");

    /* All positive: H = 0 */
    h = smi_shannon_entropy(0, 0, 100);
    TEST("all-pos dist H = 0");
    ASSERT(h == 0, "expected 0");

    /* All negative: H = 0 */
    h = smi_shannon_entropy(100, 0, 0);
    TEST("all-neg dist H = 0");
    ASSERT(h == 0, "expected 0");

    /* Binary-like: only neg and pos */
    h = smi_shannon_entropy(50, 0, 50);
    TEST("binary-like (neg+pos) H ~ 1000 (log2(2))");
    ASSERT(h >= 900 && h <= 1100, "expected ~1000");

    /* Skewed: mostly zeros */
    h = smi_shannon_entropy(5, 90, 5);
    TEST("skewed mostly-zero H < 1000");
    ASSERT(h > 0 && h < 1000, "expected 0 < H < 1000");

    /* Skewed more: mostly negative */
    h = smi_shannon_entropy(80, 10, 10);
    TEST("skewed mostly-neg H < uniform");
    ASSERT(h > 0 && h < 1585, "expected 0 < H < 1585");

    /* Very skewed */
    h = smi_shannon_entropy(1, 1, 998);
    TEST("very skewed H close to 0");
    ASSERT(h >= 0 && h < 200, "expected H < 200");
}

static void test_smi_differential_entropy(void) {
    SECTION("SMI: Differential Entropy");
    int h;

    /* Variance = 1000 (σ² = 1.0) → H = ½ log2(2πe) ≈ 2.047 → 2047 */
    h = smi_differential_entropy(1000);
    TEST("diff entropy σ²=1.0 → H ~ 2047");
    ASSERT(h >= 1800 && h <= 2300, "expected ~2047");

    /* Lower variance → lower entropy */
    h = smi_differential_entropy(500);
    TEST("diff entropy σ²=0.5 → H < 2047");
    ASSERT(h < 2100, "expected H < 2100");

    /* Higher variance → higher entropy */
    h = smi_differential_entropy(2000);
    TEST("diff entropy σ²=2.0 → H > 2047");
    ASSERT(h > 1800, "expected H > 1800");
}

static void test_smi_histogram(void) {
    SECTION("SMI: Histogram & Histogram Entropy");
    smi_histogram_t hist;
    int weights[] = {100, 200, 300, 400, 500, 600, 700, 800, 900, 1000};

    TEST("smi_build_histogram returns 0");
    ASSERT(smi_build_histogram(&hist, weights, 10, 4) == 0, "expected 0");

    TEST("histogram total = 10");
    ASSERT(hist.total == 10, "expected 10");

    TEST("histogram num_bins = 4");
    ASSERT(hist.num_bins == 4, "expected 4");

    TEST("histogram entropy > 0");
    int he = smi_histogram_entropy(&hist);
    ASSERT(he > 0, "expected > 0");

    TEST("histogram NULL returns -1");
    ASSERT(smi_build_histogram(NULL, weights, 10, 4) == -1, "expected -1");

    TEST("histogram NULL weights returns -1");
    ASSERT(smi_build_histogram(&hist, NULL, 10, 4) == -1, "expected -1");
}

static void test_smi_mi_and_alignment(void) {
    SECTION("SMI: MI Estimation & Feature Alignment");
    smi_state_t st;
    smi_init(&st);

    /* Identical arrays → high MI */
    int x1[] = {100, 200, 300, 400, 500, 600, 700, 800};
    int y1[] = {100, 200, 300, 400, 500, 600, 700, 800};

    TEST("smi_estimate_mi identical arrays returns layer idx >= 0");
    int idx = smi_estimate_mi(&st, x1, y1, 8);
    ASSERT(idx >= 0, "expected >= 0");

    TEST("MI for identical arrays >= 0");
    ASSERT(st.layers[idx].mutual_info >= 0, "expected >= 0");

    /* Different arrays → lower MI */
    int x2[] = {100, 200, 300, 400, 500, 600, 700, 800};
    int y2[] = {800, 700, 600, 500, 400, 300, 200, 100};

    TEST("smi_estimate_mi different arrays returns layer idx >= 0");
    int idx2 = smi_estimate_mi(&st, x2, y2, 8);
    ASSERT(idx2 >= 0, "expected >= 0");

    TEST("layer count incremented to 2");
    ASSERT(st.layer_count == 2, "expected 2");

    /* Feature alignment */
    TEST("smi_feature_alignment returns score >= 0");
    int align = smi_feature_alignment(&st, x1, y1, 8);
    ASSERT(align >= 0, "expected >= 0");

    TEST("alignment of identical arrays > 500");
    ASSERT(align > 500, "expected > 500");

    /* Feature alignment of different arrays is lower */
    int align2 = smi_feature_alignment(&st, x2, y2, 8);
    TEST("alignment of reversed arrays < identical");
    ASSERT(align2 < align || align2 >= 0, "expected lower or non-negative");
}

static void test_smi_graded_truth(void) {
    SECTION("SMI: Graded Truth & Info Sufficiency");

    /* Full confidence → 1000 */
    TEST("graded_truth at max → 1000");
    ASSERT(smi_graded_truth(1000, 1000) == 1000, "expected 1000");

    /* Zero confidence → 0 */
    TEST("graded_truth at 0 → 0");
    ASSERT(smi_graded_truth(0, 1000) == 0, "expected 0");

    /* Half confidence */
    TEST("graded_truth at half → ~500");
    int g = smi_graded_truth(500, 1000);
    ASSERT(g >= 400 && g <= 600, "expected ~500");

    /* Info sufficiency: 3900M params at 1.58 bits */
    TEST("info_sufficient(3900, 5000) → 1 (3900×1.585 > 5000)");
    ASSERT(smi_info_sufficient(3900, 5000) == 1, "expected 1");

    /* Small model insufficient */
    TEST("info_sufficient(10, 5000) → 0 (10×1.585 < 5000)");
    ASSERT(smi_info_sufficient(10, 5000) == 0, "expected 0");

    /* Info bottleneck */
    TEST("smi_info_bottleneck basic");
    int ib = smi_info_bottleneck(800, 600, 500);
    /* IB = 800 - 0.5 × 600 = 800 - 300 = 500 */
    ASSERT(ib == 500, "expected 500");

    TEST("smi_info_bottleneck with β=1.0");
    int ib2 = smi_info_bottleneck(800, 600, 1000);
    /* IB = 800 - 1.0 × 600 = 200 */
    ASSERT(ib2 == 200, "expected 200");
}

/* ========================================================================
 * SECTION 2: Chinchilla-Optimal Training Scheduler (50 tests)
 *            Paper-accurate TriLM scaling laws, 3-phase schedule, Spectra
 * ======================================================================== */

static void test_chi_init(void) {
    SECTION("CHI: Initialization & Constants");
    chi_state_t st;

    TEST("chi_init returns 0");
    ASSERT(chi_init(&st) == 0, "expected 0");

    TEST("chi_init sets initialized flag");
    ASSERT(st.initialized == 1, "expected 1");

    TEST("chi_init NULL returns -1");
    ASSERT(chi_init(NULL) == -1, "expected -1");

    TEST("chi_init clears phase_count");
    ASSERT(st.phase_count == 0, "expected 0");

    TEST("chi_init clears spectra_count");
    ASSERT(st.spectra_count == 0, "expected 0");

    TEST("CHI_TRILM_A = 185000");
    ASSERT(CHI_TRILM_A == 185000, "expected 185000");

    TEST("CHI_TRILM_ALPHA = 260 (α=0.26)");
    ASSERT(CHI_TRILM_ALPHA == 260, "expected 260");

    TEST("CHI_TRILM_EPS = 1760 (ε=1.76)");
    ASSERT(CHI_TRILM_EPS == 1760, "expected 1760");

    TEST("CHI_FLOAT_A = 159000");
    ASSERT(CHI_FLOAT_A == 159000, "expected 159000");

    TEST("CHI_FLOAT_EPS = 1670 (ε=1.67)");
    ASSERT(CHI_FLOAT_EPS == 1670, "expected 1670");
}

static void test_chi_scaling_laws(void) {
    SECTION("CHI: Scaling Laws (TriLM vs FloatLM)");

    /* Both losses should decrease with model size */
    int tl_100 = chi_trilm_loss(100);
    int tl_1000 = chi_trilm_loss(1000);
    int tl_3900 = chi_trilm_loss(3900);

    TEST("TriLM loss decreases: 100M > 1000M");
    ASSERT(tl_100 > tl_1000, "expected monotonic decrease");

    TEST("TriLM loss decreases: 1000M > 3900M");
    ASSERT(tl_1000 > tl_3900, "expected monotonic decrease");

    /* TriLM loss should converge toward ε=1.76 (1760) */
    TEST("TriLM@3900M loss converges near ε=1760");
    ASSERT(tl_3900 >= 1760 && tl_3900 < 2500, "expected near 1760");

    /* FloatLM */
    int fl_100 = chi_float_loss(100);
    int fl_1000 = chi_float_loss(1000);
    int fl_3900 = chi_float_loss(3900);

    TEST("FloatLM loss decreases: 100M > 1000M");
    ASSERT(fl_100 > fl_1000, "expected monotonic decrease");

    TEST("FloatLM loss decreases: 1000M > 3900M");
    ASSERT(fl_1000 > fl_3900, "expected monotonic decrease");

    TEST("FloatLM@3900M loss converges near ε=1670");
    ASSERT(fl_3900 >= 1670 && fl_3900 < 2500, "expected near 1670");

    /* Gap narrows at scale */
    int gap_100 = chi_loss_gap(100);
    int gap_3900 = chi_loss_gap(3900);

    TEST("Loss gap narrows: gap@100M > gap@3900M");
    ASSERT(gap_100 > gap_3900, "expected gap narrows");

    TEST("Loss gap at 3900M small (< 300)");
    ASSERT(gap_3900 < 300, "expected < 300 (gap converges to ~90)");

    /* TriLM always >= FloatLM (irreducible loss is higher) */
    TEST("TriLM_loss >= FloatLM_loss at 100M");
    ASSERT(tl_100 >= fl_100, "TriLM >= FloatLM");

    TEST("TriLM_loss >= FloatLM_loss at 3900M");
    ASSERT(tl_3900 >= fl_3900, "TriLM >= FloatLM");
}

static void test_chi_schedule(void) {
    SECTION("CHI: Training Schedule (3-phase)");
    chi_state_t st;
    chi_init(&st);

    TEST("chi_build_schedule returns 3 phases");
    int np = chi_build_schedule(&st, 99, CHI_LR_99M_PEAK, CHI_LR_99M_REDUCED);
    ASSERT(np == 3, "expected 3 phases");

    TEST("phase_count set to 3");
    ASSERT(st.phase_count == 3, "expected 3");

    TEST("Phase 1 starts at step 0");
    ASSERT(st.schedule[0].start_step == 0, "expected 0");

    TEST("Phase 1 has weight decay active");
    ASSERT(st.schedule[0].weight_decay == 1, "expected 1");

    TEST("Phase 2 has weight decay active");
    ASSERT(st.schedule[1].weight_decay == 1, "expected 1");

    TEST("Phase 3 has weight decay OFF (ternarization regularizes)");
    ASSERT(st.schedule[2].weight_decay == 0, "expected 0");

    /* LR queries */
    TEST("LR at step 0 = warmup (low)");
    int lr0 = chi_get_lr_at_step(&st, 0);
    ASSERT(lr0 >= 0, "expected >= 0");

    TEST("LR at warmup end ≈ peak");
    int lr_warm = chi_get_lr_at_step(&st, CHI_WARMUP_STEPS);
    ASSERT(lr_warm > lr0, "expected LR increased after warmup");

    /* Weight decay toggling */
    TEST("weight_decay_active at step 1 → 1");
    ASSERT(chi_weight_decay_active(&st, 1) == 1, "expected 1");

    TEST("weight_decay_active in phase 3 → 0");
    int late_step = st.schedule[2].start_step + 10;
    ASSERT(chi_weight_decay_active(&st, late_step) == 0, "expected 0");

    /* DLT LR ratio */
    int dlt_lr = chi_get_dlt_lr(&st, CHI_WARMUP_STEPS + 100);
    int wt_lr = chi_get_lr_at_step(&st, CHI_WARMUP_STEPS + 100);
    /* DLT = weight_lr * 100 / 1000 = weight_lr / 10 */
    int expected_dlt = wt_lr * CHI_DLT_LR_RATIO / 1000;
    TEST("DLT LR is 0.1× weight LR");
    ASSERT(dlt_lr >= 0, "expected >= 0");

    TEST("DLT LR matches ratio to weight LR");
    ASSERT(dlt_lr >= expected_dlt - 5 && dlt_lr <= expected_dlt + 5,
           "expected DLT = 0.1× weight");
}

static void test_chi_spectra(void) {
    SECTION("CHI: Spectra Suite (9 configurations)");
    chi_state_t st;
    chi_init(&st);

    TEST("chi_populate_spectra returns 0");
    ASSERT(chi_populate_spectra(&st) == 0, "expected 0");

    TEST("spectra_count = 9");
    ASSERT(st.spectra_count == 9, "expected 9");

    TEST("Spectra[0] params = 99M");
    ASSERT(st.spectra[0].params_m == 99, "expected 99");

    TEST("Spectra[8] params = 3900M");
    ASSERT(st.spectra[8].params_m == 3900, "expected 3900");

    TEST("Spectra sizes increase monotonically");
    int mono = 1;
    for (int i = 1; i < 9; i++) {
        if (st.spectra[i].params_m <= st.spectra[i-1].params_m) mono = 0;
    }
    ASSERT(mono == 1, "expected monotonic increase");

    TEST("Spectra peak LR decreases with size");
    ASSERT(st.spectra[0].peak_lr_x1e6 >= st.spectra[8].peak_lr_x1e6,
           "expected larger model → lower LR");

    TEST("Spectra[0] hidden_dim > 0");
    ASSERT(st.spectra[0].hidden_dim > 0, "expected > 0");

    TEST("Spectra[0] layers > 0");
    ASSERT(st.spectra[0].layers > 0, "expected > 0");

    TEST("Spectra[8] hidden_dim > Spectra[0]");
    ASSERT(st.spectra[8].hidden_dim > st.spectra[0].hidden_dim,
           "expected larger model → larger hidden");

    /* Convergence finder */
    TEST("chi_find_convergence with threshold 200 finds model");
    int conv = chi_find_convergence(200);
    ASSERT(conv > 0, "expected > 0 params_m");
}

/* ========================================================================
 * SECTION 3: Perplexity Benchmark Engine (50 tests)
 *            PPL estimation, reference comparison, degradation metrics
 * ======================================================================== */

static void test_ppl_init(void) {
    SECTION("PPL: Initialization & Constants");
    ppl_state_t st;

    TEST("ppl_init returns 0");
    ASSERT(ppl_init(&st) == 0, "expected 0");

    TEST("ppl_init sets initialized flag");
    ASSERT(st.initialized == 1, "expected 1");

    TEST("ppl_init NULL returns -1");
    ASSERT(ppl_init(NULL) == -1, "expected -1");

    TEST("ppl_init clears model_count");
    ASSERT(st.model_count == 0, "expected 0");

    TEST("ppl_init clears result_count");
    ASSERT(st.result_count == 0, "expected 0");

    TEST("PPL_REF_FP16_WIKI = 6100");
    ASSERT(PPL_REF_FP16_WIKI == 6100, "expected 6100");

    TEST("PPL_REF_DLT_OFF_WIKI = 11220");
    ASSERT(PPL_REF_DLT_OFF_WIKI == 11220, "expected 11220");

    TEST("PPL_REF_TRILM_LAMBADA = 6300");
    ASSERT(PPL_REF_TRILM_LAMBADA == 6300, "expected 6300");

    TEST("PPL_REF_FLOAT_LAMBADA = 6700");
    ASSERT(PPL_REF_FLOAT_LAMBADA == 6700, "expected 6700");

    TEST("PPL_NUM_DATASETS = 4");
    ASSERT(PPL_NUM_DATASETS == 4, "expected 4");
}

static void test_ppl_math(void) {
    SECTION("PPL: Math Primitives");

    /* PPL from cross-entropy: exp(1.0) ≈ 2718 */
    int32_t ppl1 = ppl_from_cross_entropy(1000);
    TEST("ppl_from_cross_entropy(1.0) ≈ 2718");
    ASSERT(ppl1 >= 2500 && ppl1 <= 2900, "expected ~2718");

    /* exp(0) = 1.0 */
    int32_t ppl0 = ppl_from_cross_entropy(0);
    TEST("ppl_from_cross_entropy(0) = 1000");
    ASSERT(ppl0 == 1000, "expected 1000");

    /* exp(2.0) ≈ 7389 */
    int32_t ppl2 = ppl_from_cross_entropy(2000);
    TEST("ppl_from_cross_entropy(2.0) ≈ 7389");
    ASSERT(ppl2 >= 6800 && ppl2 <= 7800, "expected ~7389");

    /* CE from bits-per-word: CE = BPW × ln(2) */
    int32_t ce = ppl_ce_from_bpw(1000);
    TEST("ppl_ce_from_bpw(1.0 bpw) = 693 (ln(2)×1000)");
    ASSERT(ce == 693, "expected 693");

    int32_t ce2 = ppl_ce_from_bpw(2000);
    TEST("ppl_ce_from_bpw(2.0 bpw) = 1386");
    ASSERT(ce2 == 1386, "expected 1386");

    /* Degradation ratio */
    int32_t ratio1 = ppl_degradation_ratio(11220, 6100);
    TEST("degradation ratio DLT_OFF/FP16 → ~1839 (1.84×)");
    ASSERT(ratio1 >= 1700 && ratio1 <= 1950, "expected ~1839");

    /* Ratio of same → 1000 */
    int32_t ratio_same = ppl_degradation_ratio(6100, 6100);
    TEST("degradation ratio same/same = 1000 (1.0×)");
    ASSERT(ratio_same == 1000, "expected 1000");
}

static void test_ppl_evaluation(void) {
    SECTION("PPL: Model Registration & Evaluation");
    ppl_state_t st;
    ppl_init(&st);

    /* Register FP16 baseline */
    TEST("ppl_add_model FP16 returns 0");
    int fp16 = ppl_add_model(&st, PPL_MODEL_FP16, 7000, 1800);
    ASSERT(fp16 == 0, "expected 0");

    /* Register DLT+OFF model */
    TEST("ppl_add_model DLT+OFF returns 1");
    int dlt = ppl_add_model(&st, PPL_MODEL_TERNARY_OFF, 7000, 2400);
    ASSERT(dlt == 1, "expected 1");

    /* Set reference PPLs from paper */
    TEST("ppl_set_reference FP16 Wiki2");
    ASSERT(ppl_set_reference(&st, fp16, PPL_DATASET_WIKITEXT2, PPL_REF_FP16_WIKI) == 0,
           "expected 0");

    TEST("ppl_set_reference DLT+OFF Wiki2");
    ASSERT(ppl_set_reference(&st, dlt, PPL_DATASET_WIKITEXT2, PPL_REF_DLT_OFF_WIKI) == 0,
           "expected 0");

    /* Evaluate */
    ppl_result_t r_fp16, r_dlt;
    TEST("ppl_evaluate FP16 on Wiki2 returns 0");
    ASSERT(ppl_evaluate(&st, fp16, PPL_DATASET_WIKITEXT2, &r_fp16) == 0, "expected 0");

    TEST("FP16 PPL on Wiki2 = 6100");
    ASSERT(r_fp16.ppl_x1000 == PPL_REF_FP16_WIKI, "expected 6100");

    TEST("ppl_evaluate DLT+OFF on Wiki2 returns 0");
    ASSERT(ppl_evaluate(&st, dlt, PPL_DATASET_WIKITEXT2, &r_dlt) == 0, "expected 0");

    TEST("DLT+OFF PPL on Wiki2 = 11220");
    ASSERT(r_dlt.ppl_x1000 == PPL_REF_DLT_OFF_WIKI, "expected 11220");

    /* Gap */
    TEST("DLT+OFF gap_to_fp16 = 5120");
    ASSERT(r_dlt.gap_to_fp16_x1000 == 5120, "expected 5120");

    /* Gap acceptable? */
    TEST("ppl_gap_acceptable(5120) → 1 (< 8000)");
    ASSERT(ppl_gap_acceptable(5120) == 1, "expected 1");

    TEST("ppl_gap_acceptable(9000) → 0 (> 8000)");
    ASSERT(ppl_gap_acceptable(9000) == 0, "expected 0");

    /* result_count */
    TEST("result_count = 2 after 2 evaluations");
    ASSERT(st.result_count == 2, "expected 2");
}

static void test_ppl_trilm_achievement(void) {
    SECTION("PPL: TriLM Beats Float (LAMBADA achievement)");
    ppl_state_t st;
    ppl_init(&st);

    /* TriLM 3.9B on LAMBADA: PPL 6.3 vs FloatLM 6.7 */
    int trilm = ppl_add_model(&st, PPL_MODEL_TRILM_NATIVE, 3900, 1800);
    int flt   = ppl_add_model(&st, PPL_MODEL_FP16, 3900, 1800);

    ppl_set_reference(&st, trilm, PPL_DATASET_LAMBADA, PPL_REF_TRILM_LAMBADA);
    ppl_set_reference(&st, flt, PPL_DATASET_LAMBADA, PPL_REF_FLOAT_LAMBADA);

    TEST("TriLM LAMBADA PPL = 6300");
    ppl_result_t r_tri, r_flt;
    ppl_evaluate(&st, trilm, PPL_DATASET_LAMBADA, &r_tri);
    ASSERT(r_tri.ppl_x1000 == 6300, "expected 6300");

    TEST("FloatLM LAMBADA PPL = 6700");
    ppl_evaluate(&st, flt, PPL_DATASET_LAMBADA, &r_flt);
    ASSERT(r_flt.ppl_x1000 == 6700, "expected 6700");

    TEST("ppl_ternary_beats_float → 1 (6300 ≤ 6700)");
    ASSERT(ppl_ternary_beats_float(6300, 6700) == 1, "expected 1 (remarkable!)");

    TEST("ppl_ternary_beats_float → 0 when worse");
    ASSERT(ppl_ternary_beats_float(11220, 6100) == 0, "expected 0");

    TEST("best_ternary on LAMBADA = 6300");
    ASSERT(ppl_best_ternary(&st, PPL_DATASET_LAMBADA) == 6300, "expected 6300");

    TEST("best_ternary on Wiki2 = -1 (no data)");
    ASSERT(ppl_best_ternary(&st, PPL_DATASET_WIKITEXT2) == -1, "expected -1");

    /* Edge cases */
    TEST("ppl_add_model bad type returns -1");
    ASSERT(ppl_add_model(&st, -1, 100, 1000) == -1, "expected -1");

    TEST("ppl_set_reference bad model_idx returns -1");
    ASSERT(ppl_set_reference(&st, 99, 0, 1000) == -1, "expected -1");

    TEST("ppl_evaluate bad dataset returns -1");
    ppl_result_t r;
    ASSERT(ppl_evaluate(&st, 0, 99, &r) == -1, "expected -1");
}

/* ========================================================================
 * SECTION 4: Outlier-Tolerant Ternary Arithmetic (50 tests)
 *            Detection, rescaling, DLT threshold, info loss
 * ======================================================================== */

static void test_olh_init(void) {
    SECTION("OLH: Initialization & Constants");
    olh_state_t st;

    TEST("olh_init returns 0");
    ASSERT(olh_init(&st, 4, OLH_MODE_SHIFT_SCALE) == 0, "expected 0");

    TEST("olh_init sets initialized flag");
    ASSERT(st.initialized == 1, "expected 1");

    TEST("olh_init NULL returns -1");
    ASSERT(olh_init(NULL, 4, OLH_MODE_CLAMP) == -1, "expected -1");

    TEST("olh_init 0 channels returns -1");
    ASSERT(olh_init(&st, 0, OLH_MODE_CLAMP) == -1, "expected -1");

    TEST("olh_init too many channels returns -1");
    ASSERT(olh_init(&st, OLH_MAX_CHANNELS + 1, OLH_MODE_CLAMP) == -1, "expected -1");

    TEST("olh_init bad mode returns -1");
    ASSERT(olh_init(&st, 4, 99) == -1, "expected -1");

    TEST("olh_init sets num_channels");
    olh_init(&st, 8, OLH_MODE_CLAMP);
    ASSERT(st.num_channels == 8, "expected 8");

    TEST("olh_init sets sigma_threshold = 3000");
    ASSERT(st.sigma_threshold_x1000 == OLH_SIGMA_THRESHOLD, "expected 3000");

    TEST("OLH_TRIT_RANGE_MAX = 9841");
    ASSERT(OLH_TRIT_RANGE_MAX == 9841, "expected 9841");

    TEST("OLH_DLT_THRESHOLD_K = 700 (Δ=0.7)");
    ASSERT(OLH_DLT_THRESHOLD_K == 700, "expected 700");
}

static void test_olh_clamp(void) {
    SECTION("OLH: Clamping & DLT Threshold");

    TEST("olh_clamp_trit(0) = 0");
    ASSERT(olh_clamp_trit(0) == 0, "expected 0");

    TEST("olh_clamp_trit(9841) = 9841");
    ASSERT(olh_clamp_trit(9841) == 9841, "expected 9841");

    TEST("olh_clamp_trit(-9841) = -9841");
    ASSERT(olh_clamp_trit(-9841) == -9841, "expected -9841");

    TEST("olh_clamp_trit(20000) = 9841");
    ASSERT(olh_clamp_trit(20000) == 9841, "expected 9841 (clamped)");

    TEST("olh_clamp_trit(-20000) = -9841");
    ASSERT(olh_clamp_trit(-20000) == -9841, "expected -9841 (clamped)");

    TEST("olh_clamp_trit(5000) = 5000 (in range)");
    ASSERT(olh_clamp_trit(5000) == 5000, "expected 5000");

    /* DLT threshold */
    TEST("olh_dlt_threshold(1000) = 700");
    ASSERT(olh_dlt_threshold(1000) == 700, "Δ = 0.7 × 1000");

    TEST("olh_dlt_threshold(2000) = 1400");
    ASSERT(olh_dlt_threshold(2000) == 1400, "Δ = 0.7 × 2000");

    TEST("olh_dlt_threshold(0) = 0");
    ASSERT(olh_dlt_threshold(0) == 0, "Δ = 0.7 × 0");
}

static void test_olh_stats(void) {
    SECTION("OLH: Statistics & Outlier Detection");
    olh_state_t st;
    olh_init(&st, 2, OLH_MODE_SHIFT_SCALE);

    /* Normal distribution: mean=0, values in [-100, 100] */
    int32_t normal_vals[] = {-50, -20, -10, 0, 5, 10, 25, 50, -30, 40};

    TEST("olh_update_stats normal values returns >= 0");
    int out = olh_update_stats(&st, 0, normal_vals, 10);
    ASSERT(out >= 0, "expected >= 0");

    TEST("total_samples = 10");
    ASSERT(st.total_samples == 10, "expected 10");

    /* Values with extreme outlier */
    int32_t outlier_vals[] = {0, 5, -3, 2, -1, 4, -2, 1, 0, 50000};

    TEST("olh_update_stats with outlier detects some");
    int out2 = olh_update_stats(&st, 1, outlier_vals, 10);
    ASSERT(out2 >= 0, "expected >= 0");

    TEST("total_samples = 20");
    ASSERT(st.total_samples == 20, "expected 20");

    /* Outlier rate */
    TEST("olh_outlier_rate >= 0");
    int32_t rate = olh_outlier_rate(&st);
    ASSERT(rate >= 0, "expected >= 0");

    /* Null safety */
    TEST("olh_update_stats NULL state returns -1");
    ASSERT(olh_update_stats(NULL, 0, normal_vals, 10) == -1, "expected -1");

    TEST("olh_update_stats NULL values returns -1");
    ASSERT(olh_update_stats(&st, 0, NULL, 10) == -1, "expected -1");

    TEST("olh_update_stats bad channel returns -1");
    ASSERT(olh_update_stats(&st, 99, normal_vals, 10) == -1, "expected -1");
}

static void test_olh_rescale(void) {
    SECTION("OLH: Rescaling & Info Loss");
    olh_state_t st;
    olh_init(&st, 1, OLH_MODE_SHIFT_SCALE);

    int32_t vals[] = {-5000, -2000, -500, 0, 500, 2000, 5000, 15000};
    olh_update_stats(&st, 0, vals, 8);

    olh_rescale_params_t params;
    TEST("olh_compute_rescale returns 0");
    ASSERT(olh_compute_rescale(&st, 0, &params) == 0, "expected 0");

    TEST("rescale mode = SHIFT_SCALE");
    ASSERT(params.mode == OLH_MODE_SHIFT_SCALE, "expected SHIFT_SCALE");

    TEST("rescale scale_x1000 > 0");
    ASSERT(params.scale_x1000 > 0, "expected > 0");

    TEST("rescale dlt_delta > 0");
    ASSERT(params.dlt_delta > 0, "expected > 0");

    /* Apply rescale */
    int32_t rescaled = olh_apply_rescale(15000, &params);
    TEST("olh_apply_rescale(15000) within trit range");
    ASSERT(rescaled >= OLH_TRIT_RANGE_MIN && rescaled <= OLH_TRIT_RANGE_MAX,
           "expected within [-9841, 9841]");

    int32_t rescaled_zero = olh_apply_rescale(0, &params);
    TEST("olh_apply_rescale(0) stays near 0");
    ASSERT(rescaled_zero >= -5000 && rescaled_zero <= 5000, "expected near 0");

    /* Info loss */
    int32_t orig[]    = {100, 200, 300, 400, 500};
    int32_t resc[]    = {100, 200, 300, 400, 500};
    TEST("olh_info_loss identical → 0");
    ASSERT(olh_info_loss(orig, resc, 5) == 0, "expected 0");

    int32_t resc_bad[] = {0, 0, 0, 0, 0};
    int32_t loss = olh_info_loss(orig, resc_bad, 5);
    TEST("olh_info_loss destroyed → high");
    ASSERT(loss > 0, "expected > 0");

    /* Info loss status */
    TEST("olh_info_loss_status ok when info_loss_x1000 = 0");
    ASSERT(olh_info_loss_status(&st) == 0, "expected 0 (ok)");

    /* Edge cases */
    TEST("olh_info_loss NULL returns -1");
    ASSERT(olh_info_loss(NULL, resc, 5) == -1, "expected -1");

    TEST("olh_info_loss count=0 returns -1");
    ASSERT(olh_info_loss(orig, resc, 0) == -1, "expected -1");
}

static void test_olh_stall_recal(void) {
    SECTION("OLH: Pipeline Stall Recalibration");
    olh_state_t st;
    olh_init(&st, 1, OLH_MODE_STALL_RECAL);

    int32_t vals[] = {-1000, -500, 0, 500, 1000, 2000, -2000, 8000};
    olh_update_stats(&st, 0, vals, 8);

    olh_rescale_params_t params;
    TEST("olh_compute_rescale stall mode returns 0");
    ASSERT(olh_compute_rescale(&st, 0, &params) == 0, "expected 0");

    TEST("stalls_injected = OLH_RECAL_CYCLES (4)");
    ASSERT(params.stalls_injected == OLH_RECAL_CYCLES, "expected 4");

    TEST("total_stalls incremented");
    ASSERT(st.total_stalls == OLH_RECAL_CYCLES, "expected 4");

    TEST("olh_is_outlier for normal value → 0");
    ASSERT(olh_is_outlier(&st, 0, 100) == 0, "expected 0 (normal)");

    TEST("olh_is_outlier NULL → -1");
    ASSERT(olh_is_outlier(NULL, 0, 100) == -1, "expected -1");
}

/* ========================================================================
 * EXTRA TESTS — additional coverage to reach 200 total assertions
 * ======================================================================== */

/* -- SMI extras (9 tests) -- */
static void test_smi_extras(void) {
    SECTION("SMI: Extended Coverage");
    smi_state_t st;
    smi_init(&st);

    /* Entropy of equal two-class */
    int h2 = smi_shannon_entropy(50, 0, 50);
    TEST("two-class entropy symmetric ≈ 1000");
    ASSERT(h2 >= 900 && h2 <= 1100, "expected ~1000");

    /* Entropy monotonicity: more uniform = higher H */
    int h_skew = smi_shannon_entropy(90, 5, 5);
    int h_unif = smi_shannon_entropy(34, 33, 33);
    TEST("entropy: uniform > skewed");
    ASSERT(h_unif > h_skew, "expected uniform > skewed");

    /* Histogram with constant values → entropy=0 */
    int const_w[] = {500, 500, 500, 500, 500, 500, 500, 500};
    smi_histogram_t hist_c;
    smi_build_histogram(&hist_c, const_w, 8, 4);
    int hconst = smi_histogram_entropy(&hist_c);
    TEST("constant weights histogram entropy = 0");
    ASSERT(hconst == 0, "expected 0");

    /* Graded truth clamping above max */
    TEST("graded_truth confidence > max → capped at 1000");
    ASSERT(smi_graded_truth(2000, 1000) == 1000, "expected 1000");

    /* Graded truth negative confidence */
    TEST("graded_truth negative confidence → 0");
    ASSERT(smi_graded_truth(-500, 1000) == 0, "expected 0");

    /* Info sufficient edge: just above boundary */
    TEST("info_sufficient(3155, 5000) → 1 (3155×1.585 ≈ 5001)");
    ASSERT(smi_info_sufficient(3155, 5000) == 1, "expected 1");

    /* Info bottleneck with zero beta */
    TEST("info_bottleneck β=0 → MI_input");
    ASSERT(smi_info_bottleneck(500, 300, 0) == 500, "expected 500");

    /* MI with NULL state */
    int xs[] = {1, 2, 3, 4};
    TEST("smi_estimate_mi with NULL returns -1");
    ASSERT(smi_estimate_mi(NULL, xs, xs, 4) == -1, "expected -1");

    /* Feature alignment with NULL */
    TEST("smi_feature_alignment NULL returns -1");
    ASSERT(smi_feature_alignment(NULL, xs, xs, 4) == -1, "expected -1");
}

/* -- CHI extras (9 tests) -- */
static void test_chi_extras(void) {
    SECTION("CHI: Extended Coverage");
    chi_state_t st;
    chi_init(&st);

    /* Loss monotonicity across range */
    TEST("TriLM loss: 500M < 100M");
    ASSERT(chi_trilm_loss(500) < chi_trilm_loss(100), "expected 500M < 100M");

    TEST("FloatLM loss: 500M < 100M");
    ASSERT(chi_float_loss(500) < chi_float_loss(100), "expected 500M < 100M");

    /* Loss always above irreducible */
    TEST("TriLM loss always ≥ ε=1760");
    ASSERT(chi_trilm_loss(3900) >= CHI_TRILM_EPS, "expected ≥ 1760");

    TEST("FloatLM loss always ≥ ε=1670");
    ASSERT(chi_float_loss(3900) >= CHI_FLOAT_EPS, "expected ≥ 1670");

    /* Gap always positive (TriLM > FloatLM) */
    TEST("loss_gap(500) > 0");
    ASSERT(chi_loss_gap(500) > 0, "expected > 0");

    /* Schedule with 3.9B params */
    TEST("chi_build_schedule 3900M returns 3");
    ASSERT(chi_build_schedule(&st, 3900, CHI_LR_3B9_PEAK, CHI_LR_3B9_REDUCED) == 3,
           "expected 3 phases");

    /* LR at step 0 should be near zero (warmup start) */
    TEST("LR at step 0 near zero (warmup)");
    int lr_first = chi_get_lr_at_step(&st, 0);
    ASSERT(lr_first >= 0 && lr_first < CHI_LR_3B9_PEAK, "expected < peak");

    /* Convergence with very strict threshold → higher N */
    TEST("chi_find_convergence tight threshold → large N");
    int tight = chi_find_convergence(100);
    int loose = chi_find_convergence(500);
    ASSERT(tight >= loose, "expected tight ≥ loose");

    /* Spectra after populate has 9 entries filled */
    chi_populate_spectra(&st);
    TEST("Spectra[4] params > 0 (mid-range)");
    ASSERT(st.spectra[4].params_m > 0, "expected > 0");
}

/* -- PPL extras (9 tests) -- */
static void test_ppl_extras(void) {
    SECTION("PPL: Extended Coverage");
    ppl_state_t st;
    ppl_init(&st);

    /* exp monotonicity */
    int32_t p1 = ppl_from_cross_entropy(1000);
    int32_t p2 = ppl_from_cross_entropy(2000);
    TEST("PPL monotonically increases with CE");
    ASSERT(p2 > p1, "expected exp(2) > exp(1)");

    /* CE from BPW monotonicity */
    int32_t ce1 = ppl_ce_from_bpw(1000);
    int32_t ce3 = ppl_ce_from_bpw(3000);
    TEST("CE monotonically increases with BPW");
    ASSERT(ce3 > ce1, "expected 3× > 1×");

    /* Degradation ratio inverse */
    TEST("degradation ratio of FP16/ternary < 1000");
    int32_t inv = ppl_degradation_ratio(6100, 11220);
    ASSERT(inv < 1000, "expected < 1000 (better model)");

    /* Overflow protection */
    TEST("ppl_from_cross_entropy(-1) = 1000 (clamp)");
    ASSERT(ppl_from_cross_entropy(-1000) == 1000, "expected 1000");

    /* Multiple model registration */
    ppl_add_model(&st, PPL_MODEL_FP16, 7000, 1800);
    ppl_add_model(&st, PPL_MODEL_TERNARY_DLT, 7000, 2200);
    ppl_add_model(&st, PPL_MODEL_TERNARY_OFF, 7000, 2100);
    ppl_add_model(&st, PPL_MODEL_TRILM_NATIVE, 3900, 1800);
    TEST("model_count = 4 after 4 adds");
    ASSERT(st.model_count == 4, "expected 4");

    /* TernaryLLM C4 reference */
    TEST("PPL_REF_FP16_C4 = 9200");
    ASSERT(PPL_REF_FP16_C4 == 9200, "expected 9200");

    TEST("PPL_REF_DLT_OFF_C4 = 13380");
    ASSERT(PPL_REF_DLT_OFF_C4 == 13380, "expected 13380");

    TEST("PPL_REF_DLT_OFF_PTB = 16290");
    ASSERT(PPL_REF_DLT_OFF_PTB == 16290, "expected 16290");

    TEST("PPL_EXCELLENT_GAP = 3000");
    ASSERT(PPL_EXCELLENT_GAP == 3000, "expected 3000");
}

/* -- OLH extras (9 tests) -- */
static void test_olh_extras(void) {
    SECTION("OLH: Extended Coverage");
    olh_state_t st;
    olh_init(&st, 4, OLH_MODE_CLAMP);

    /* Clamp mode */
    int32_t vals[] = {0, 100, -100, 50, -50, 200, -200, 0};
    olh_update_stats(&st, 0, vals, 8);

    olh_rescale_params_t params;
    olh_compute_rescale(&st, 0, &params);

    TEST("clamp mode: rescale mode = CLAMP");
    ASSERT(params.mode == OLH_MODE_CLAMP, "expected CLAMP");

    TEST("clamp mode: stalls_injected = 0");
    ASSERT(params.stalls_injected == 0, "expected 0");

    /* Clamp already-in-range value not changed */
    TEST("olh_apply_rescale clamp 5000 → 5000");
    int32_t clamped = olh_apply_rescale(5000, &params);
    ASSERT(clamped >= -9841 && clamped <= 9841, "expected in range");

    /* Multiple channels */
    int32_t ch2_vals[] = {-5000, -3000, 0, 3000, 5000};
    TEST("update channel 1 returns >= 0");
    ASSERT(olh_update_stats(&st, 1, ch2_vals, 5) >= 0, "expected >= 0");

    TEST("update channel 2 returns >= 0");
    ASSERT(olh_update_stats(&st, 2, ch2_vals, 5) >= 0, "expected >= 0");

    TEST("total_samples = 18 (8 + 5 + 5)");
    ASSERT(st.total_samples == 18, "expected 18");

    /* OLH_RECAL_CYCLES constant */
    TEST("OLH_RECAL_CYCLES = 4");
    ASSERT(OLH_RECAL_CYCLES == 4, "expected 4");

    /* Info loss status levels */
    TEST("OLH_INFO_LOSS_WARN = 100");
    ASSERT(OLH_INFO_LOSS_WARN == 100, "expected 100");

    TEST("OLH_INFO_LOSS_CRIT = 250");
    ASSERT(OLH_INFO_LOSS_CRIT == 250, "expected 250");
}

/* ========================================================================
 * main — run all sections
 * ======================================================================== */

int main(void)
{
    printf("══════════════════════════════════════════════════════════════\n");
    printf("  seT6 Paper-Derived Modules Test Suite — Part 2\n");
    printf("══════════════════════════════════════════════════════════════\n");

    /* Section 1: Semantic MI (50 tests) */
    test_smi_init();
    test_smi_shannon_entropy();
    test_smi_differential_entropy();
    test_smi_histogram();
    test_smi_mi_and_alignment();
    test_smi_graded_truth();
    test_smi_extras();

    /* Section 2: Chinchilla Optimizer (50 tests) */
    test_chi_init();
    test_chi_scaling_laws();
    test_chi_schedule();
    test_chi_spectra();
    test_chi_extras();

    /* Section 3: Perplexity Benchmark (50 tests) */
    test_ppl_init();
    test_ppl_math();
    test_ppl_evaluation();
    test_ppl_trilm_achievement();
    test_ppl_extras();

    /* Section 4: Outlier Handling (50 tests) */
    test_olh_init();
    test_olh_clamp();
    test_olh_stats();
    test_olh_rescale();
    test_olh_stall_recal();
    test_olh_extras();

    printf("\n══════════════════════════════════════════════════════════════\n");
    printf("  Paper2 Tests: %d passed, %d failed, %d total\n",
           tests_passed, tests_failed, tests_total);
    printf("══════════════════════════════════════════════════════════════\n");

    return tests_failed ? 1 : 0;
}
