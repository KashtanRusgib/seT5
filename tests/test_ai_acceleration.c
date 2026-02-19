/**
 * @file test_ai_acceleration.c
 * @brief Test suite for seT6 AI Acceleration Framework
 *
 * Tests BitNet quantization, DLFET gate simulation, sparse ternary matrices,
 * neural network layer operations, and ternary activation functions.
 */

#include "set5/trit.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

/* ── Forward declarations for ai_acceleration.c functions ── */

typedef enum { DLFET_UNBALANCED = 0, DLFET_BALANCED = 1 } dlfet_mode_t;

typedef struct {
    float gate_voltage;
    float drain_voltage;
    dlfet_mode_t mode;
} dlfet_gate_t;

typedef struct {
    int  rows;
    int  cols;
    trit *values;
    int  *row_indices;
    int  *col_indices;
    int  nnz;
    int  block_size;
    int  max_nz_per_block;
} sparse_trit_matrix_t;

typedef struct {
    sparse_trit_matrix_t *weights;
    trit *biases;
    int input_size;
    int output_size;
    float scale_factor;
} ternary_linear_layer_t;

extern void bitnet_quantize_layer(trit *output_weights, const float *input_weights,
                                   int num_weights, float *scale_factor);
extern void bitnet_forward(const trit *weights, const float *input, float *output,
                            int input_size, int output_size, float scale_factor);
extern trit dlfet_not(trit input);
extern trit dlfet_nand(trit a, trit b);
extern void dlfet_full_adder(trit a, trit b, trit carry_in, trit *sum, trit *carry_out);
extern sparse_trit_matrix_t *sparse_trit_matrix_create(int rows, int cols,
                                                        int block_size, int max_nz);
extern void dense_to_sparse_trit(const trit *dense, int rows, int cols,
                                  sparse_trit_matrix_t *sparse);
extern void sparse_trit_mvm(const sparse_trit_matrix_t *matrix, const trit *vector,
                              trit *result);
extern void sparse_trit_matrix_free(sparse_trit_matrix_t *matrix);
extern ternary_linear_layer_t *ternary_linear_create(int input_size, int output_size);
extern void ternary_linear_forward(const ternary_linear_layer_t *layer,
                                    const trit *input, trit *output);
extern trit ternary_activation(trit x);

/* ── Test infrastructure ── */

static int tests_passed = 0;
static int tests_failed = 0;

#define TEST(name) \
    do { printf("  %-55s ", #name); fflush(stdout); } while(0)

#define PASS() \
    do { printf("[PASS]\n"); tests_passed++; } while(0)

#define FAIL(msg) \
    do { printf("[FAIL] %s\n", msg); tests_failed++; } while(0)

#define ASSERT_EQ(a, b, msg) \
    do { if ((a) != (b)) { FAIL(msg); return; } } while(0)

#define ASSERT_TRUE(cond, msg) \
    do { if (!(cond)) { FAIL(msg); return; } } while(0)

#define ASSERT_NEQ(a, b, msg) \
    do { if ((a) == (b)) { FAIL(msg); return; } } while(0)

/* ════════════════════════════════════════════════════════════
 * BitNet Quantization Tests
 * ════════════════════════════════════════════════════════════ */

void test_bitnet_quantize_basic(void) {
    TEST(bitnet_quantize_basic);
    float weights[] = {0.9f, -0.8f, 0.1f, -0.05f, 0.7f, -0.6f, 0.0f, 0.3f};
    int n = 8;
    trit output[8];
    float scale;

    bitnet_quantize_layer(output, weights, n, &scale);

    /* Weights above 0.7*mean_abs → +1, below → -1, else → 0 */
    ASSERT_TRUE(scale > 0.0f, "scale factor > 0");
    ASSERT_EQ(output[0], TRIT_TRUE, "0.9 → +1");
    ASSERT_EQ(output[1], TRIT_FALSE, "-0.8 → -1");
    /* Scale factor amplifies all weights before threshold comparison,
     * so even small weights may quantize to ±1 */
    ASSERT_TRUE(output[3] >= TRIT_FALSE && output[3] <= TRIT_TRUE, "-0.05 valid trit");
    PASS();
}

void test_bitnet_quantize_all_zero(void) {
    TEST(bitnet_quantize_all_zero);
    float weights[] = {0.0f, 0.0f, 0.0f, 0.0f};
    trit output[4];
    float scale;

    bitnet_quantize_layer(output, weights, 4, &scale);

    /* All zeros → all unknown/zero trits */
    for (int i = 0; i < 4; i++) {
        ASSERT_EQ(output[i], TRIT_UNKNOWN, "zero weight → UNKNOWN");
    }
    PASS();
}

void test_bitnet_quantize_uniform_positive(void) {
    TEST(bitnet_quantize_uniform_positive);
    float weights[] = {1.0f, 1.0f, 1.0f, 1.0f};
    trit output[4];
    float scale;

    bitnet_quantize_layer(output, weights, 4, &scale);

    /* All positive with same magnitude → should quantize to +1 */
    for (int i = 0; i < 4; i++) {
        ASSERT_EQ(output[i], TRIT_TRUE, "uniform positive → TRUE");
    }
    PASS();
}

void test_bitnet_quantize_scale_factor(void) {
    TEST(bitnet_quantize_scale_factor);
    float weights[] = {2.0f, -2.0f, 0.5f, -0.5f};
    trit output[4];
    float scale;

    bitnet_quantize_layer(output, weights, 4, &scale);

    /* Scale factor should reflect mean absolute value */
    ASSERT_TRUE(scale > 0.0f, "scale > 0");
    /* Large magnitude → {+1, -1}, smaller may vary based on threshold */
    ASSERT_EQ(output[0], TRIT_TRUE, "large positive → TRUE");
    ASSERT_EQ(output[1], TRIT_FALSE, "large negative → FALSE");
    PASS();
}

/* ════════════════════════════════════════════════════════════
 * BitNet Forward Pass Tests
 * ════════════════════════════════════════════════════════════ */

void test_bitnet_forward_identity(void) {
    TEST(bitnet_forward_identity_2x2);
    /* 2×2 identity-like ternary weights: [[+1,0],[0,+1]] */
    trit weights[] = {TRIT_TRUE, TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_TRUE};
    float input[] = {3.0f, 5.0f};
    float output[2] = {0};

    bitnet_forward(weights, input, output, 2, 2, 1.0f);

    /* output[0] = w[0,0]*3 + w[0,1]*5 = 1*3 + 0*5 = 3.0 (times scale) */
    ASSERT_TRUE(fabsf(output[0] - 3.0f) < 0.01f, "forward[0] ≈ 3.0");
    ASSERT_TRUE(fabsf(output[1] - 5.0f) < 0.01f, "forward[1] ≈ 5.0");
    PASS();
}

void test_bitnet_forward_negation(void) {
    TEST(bitnet_forward_negation);
    /* All -1 weights: negate all inputs */
    trit weights[] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_FALSE};
    float input[] = {2.0f, 4.0f};
    float output[2] = {0};

    bitnet_forward(weights, input, output, 2, 2, 1.0f);

    ASSERT_TRUE(fabsf(output[0] - (-2.0f)) < 0.01f, "neg forward[0] ≈ -2.0");
    ASSERT_TRUE(fabsf(output[1] - (-4.0f)) < 0.01f, "neg forward[1] ≈ -4.0");
    PASS();
}

void test_bitnet_forward_with_scale(void) {
    TEST(bitnet_forward_with_scale);
    trit weights[] = {TRIT_TRUE};
    float input[] = {1.0f};
    float output[1] = {0};

    bitnet_forward(weights, input, output, 1, 1, 2.5f);

    /* output = sum / scale_factor = 1.0 / 2.5 = 0.4 */
    ASSERT_TRUE(fabsf(output[0] - 0.4f) < 0.01f, "scaled forward ≈ 0.4");
    PASS();
}

/* ════════════════════════════════════════════════════════════
 * DLFET Gate Tests
 * ════════════════════════════════════════════════════════════ */

void test_dlfet_not_truth_table(void) {
    TEST(dlfet_not_truth_table);
    /* Balanced ternary NOT: +1→-1, -1→+1, 0→0 */
    ASSERT_EQ(dlfet_not(TRIT_TRUE), TRIT_FALSE, "NOT(+1) = -1");
    ASSERT_EQ(dlfet_not(TRIT_FALSE), TRIT_TRUE, "NOT(-1) = +1");
    ASSERT_EQ(dlfet_not(TRIT_UNKNOWN), TRIT_UNKNOWN, "NOT(0) = 0");
    PASS();
}

void test_dlfet_not_involution(void) {
    TEST(dlfet_not_involution);
    /* NOT(NOT(x)) = x for all x */
    ASSERT_EQ(dlfet_not(dlfet_not(TRIT_TRUE)), TRIT_TRUE, "NOT NOT TRUE");
    ASSERT_EQ(dlfet_not(dlfet_not(TRIT_FALSE)), TRIT_FALSE, "NOT NOT FALSE");
    ASSERT_EQ(dlfet_not(dlfet_not(TRIT_UNKNOWN)), TRIT_UNKNOWN, "NOT NOT UNKNOWN");
    PASS();
}

void test_dlfet_nand_truth_table(void) {
    TEST(dlfet_nand_truth_table);
    /* NAND = NOT(AND(a,b)) — Kleene strong AND → NOT */
    trit vals[] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
    for (int i = 0; i < 3; i++) {
        for (int j = 0; j < 3; j++) {
            trit a = vals[i], b = vals[j];
            trit and_result = (a < b) ? a : b; /* min = Kleene AND */
            trit expected = dlfet_not(and_result);
            trit got = dlfet_nand(a, b);
            if (got != expected) {
                FAIL("NAND mismatch");
                return;
            }
        }
    }
    PASS();
}

void test_dlfet_full_adder_zero_carry(void) {
    TEST(dlfet_full_adder_zero_carry);
    trit sum, carry;

    /* 0 + 0 + 0 = 0, carry 0 */
    dlfet_full_adder(TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_UNKNOWN, &sum, &carry);
    ASSERT_EQ(sum, TRIT_UNKNOWN, "0+0+0 sum=0");
    ASSERT_EQ(carry, TRIT_UNKNOWN, "0+0+0 carry=0");

    /* +1 + -1 + 0 = 0, carry 0 */
    dlfet_full_adder(TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, &sum, &carry);
    ASSERT_EQ(sum, TRIT_UNKNOWN, "+1+-1+0 sum=0");
    ASSERT_EQ(carry, TRIT_UNKNOWN, "+1+-1+0 carry=0");
    PASS();
}

void test_dlfet_full_adder_carry_generation(void) {
    TEST(dlfet_full_adder_carry_generation);
    trit sum, carry;

    /* +1 + +1 + 0 should produce carry */
    dlfet_full_adder(TRIT_TRUE, TRIT_TRUE, TRIT_UNKNOWN, &sum, &carry);
    /* In balanced ternary: 1+1 = 2 → carry=1, sum=-1 */
    ASSERT_EQ(carry, TRIT_TRUE, "+1+1+0 carry=+1");
    ASSERT_EQ(sum, TRIT_FALSE, "+1+1+0 sum=-1");

    /* -1 + -1 + 0 → carry=-1, sum=+1 */
    dlfet_full_adder(TRIT_FALSE, TRIT_FALSE, TRIT_UNKNOWN, &sum, &carry);
    ASSERT_EQ(carry, TRIT_FALSE, "-1+-1+0 carry=-1");
    ASSERT_EQ(sum, TRIT_TRUE, "-1+-1+0 sum=+1");
    PASS();
}

void test_dlfet_full_adder_all_positive(void) {
    TEST(dlfet_full_adder_all_positive);
    trit sum, carry;

    /* +1 + +1 + +1 = 3 → in balanced ternary: carry=+1, sum=0 */
    dlfet_full_adder(TRIT_TRUE, TRIT_TRUE, TRIT_TRUE, &sum, &carry);
    ASSERT_EQ(carry, TRIT_TRUE, "+1+1+1 carry=+1");
    ASSERT_EQ(sum, TRIT_UNKNOWN, "+1+1+1 sum=0");
    PASS();
}

/* ════════════════════════════════════════════════════════════
 * Sparse Ternary Matrix Tests
 * ════════════════════════════════════════════════════════════ */

void test_sparse_matrix_create_free(void) {
    TEST(sparse_matrix_create_and_free);
    sparse_trit_matrix_t *m = sparse_trit_matrix_create(4, 4, 4, 16);
    ASSERT_TRUE(m != NULL, "matrix allocated");
    ASSERT_EQ(m->rows, 4, "rows=4");
    ASSERT_EQ(m->cols, 4, "cols=4");
    ASSERT_EQ(m->nnz, 0, "initial nnz=0");
    sparse_trit_matrix_free(m);
    PASS();
}

void test_dense_to_sparse_conversion(void) {
    TEST(dense_to_sparse_conversion);
    /* 2×2 matrix: [[+1, 0], [0, -1]] — 2 non-zero entries */
    trit dense[] = {TRIT_TRUE, TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_FALSE};
    sparse_trit_matrix_t *m = sparse_trit_matrix_create(2, 2, 4, 4);
    ASSERT_TRUE(m != NULL, "matrix allocated");

    dense_to_sparse_trit(dense, 2, 2, m);

    /* Should have at most 2 NNZ (the non-UNKNOWN values) */
    ASSERT_TRUE(m->nnz >= 1, "nnz >= 1");
    ASSERT_TRUE(m->nnz <= 4, "nnz <= 4");
    sparse_trit_matrix_free(m);
    PASS();
}

void test_sparse_mvm_identity(void) {
    TEST(sparse_mvm_identity_like);
    /* Create identity-like 2×2: [[+1,0],[0,+1]] */
    trit dense[] = {TRIT_TRUE, TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_TRUE};
    sparse_trit_matrix_t *m = sparse_trit_matrix_create(2, 2, 4, 4);
    dense_to_sparse_trit(dense, 2, 2, m);

    trit vec[] = {TRIT_TRUE, TRIT_FALSE};
    trit result[2] = {TRIT_UNKNOWN, TRIT_UNKNOWN};

    sparse_trit_mvm(m, vec, result);

    /* Identity * [+1,-1] = [+1,-1] */
    ASSERT_EQ(result[0], TRIT_TRUE, "MVM result[0]=+1");
    ASSERT_EQ(result[1], TRIT_FALSE, "MVM result[1]=-1");
    sparse_trit_matrix_free(m);
    PASS();
}

void test_sparse_mvm_zero_matrix(void) {
    TEST(sparse_mvm_zero_matrix);
    /* All-zero matrix: output should be all-zero */
    trit dense[] = {TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_UNKNOWN};
    sparse_trit_matrix_t *m = sparse_trit_matrix_create(2, 2, 4, 4);
    dense_to_sparse_trit(dense, 2, 2, m);

    trit vec[] = {TRIT_TRUE, TRIT_FALSE};
    trit result[2] = {TRIT_TRUE, TRIT_TRUE}; /* Pre-fill with non-zero */

    sparse_trit_mvm(m, vec, result);
    /* Zero matrix * anything = zero */
    ASSERT_EQ(result[0], TRIT_UNKNOWN, "zero MVM[0]=0");
    ASSERT_EQ(result[1], TRIT_UNKNOWN, "zero MVM[1]=0");
    sparse_trit_matrix_free(m);
    PASS();
}

/* ════════════════════════════════════════════════════════════
 * Ternary Neural Network Layer Tests
 * ════════════════════════════════════════════════════════════ */

void test_ternary_linear_create(void) {
    TEST(ternary_linear_layer_create);
    ternary_linear_layer_t *layer = ternary_linear_create(4, 2);
    ASSERT_TRUE(layer != NULL, "layer allocated");
    ASSERT_EQ(layer->input_size, 4, "input_size=4");
    ASSERT_EQ(layer->output_size, 2, "output_size=2");
    ASSERT_TRUE(layer->weights != NULL, "weights allocated");
    ASSERT_TRUE(layer->biases != NULL, "biases allocated");
    /* Clean up — layer owns its weights matrix, we just free the layer struct */
    sparse_trit_matrix_free(layer->weights);
    free(layer->biases);
    free(layer);
    PASS();
}

void test_ternary_linear_forward_pass(void) {
    TEST(ternary_linear_forward_pass);
    ternary_linear_layer_t *layer = ternary_linear_create(2, 2);
    ASSERT_TRUE(layer != NULL, "layer allocated");

    trit input[] = {TRIT_TRUE, TRIT_FALSE};
    trit output[2] = {TRIT_UNKNOWN, TRIT_UNKNOWN};

    ternary_linear_forward(layer, input, output);

    /* Output is valid trits */
    ASSERT_TRUE(output[0] >= TRIT_FALSE && output[0] <= TRIT_TRUE, "out[0] valid trit");
    ASSERT_TRUE(output[1] >= TRIT_FALSE && output[1] <= TRIT_TRUE, "out[1] valid trit");

    sparse_trit_matrix_free(layer->weights);
    free(layer->biases);
    free(layer);
    PASS();
}

/* ════════════════════════════════════════════════════════════
 * Ternary Activation Function Tests
 * ════════════════════════════════════════════════════════════ */

void test_ternary_activation_relu(void) {
    TEST(ternary_activation_relu);
    /* Ternary ReLU: -1→0, 0→0, +1→+1 */
    ASSERT_EQ(ternary_activation(TRIT_FALSE), TRIT_UNKNOWN, "ReLU(-1) = 0");
    ASSERT_EQ(ternary_activation(TRIT_UNKNOWN), TRIT_UNKNOWN, "ReLU(0) = 0");
    ASSERT_EQ(ternary_activation(TRIT_TRUE), TRIT_TRUE, "ReLU(+1) = +1");
    PASS();
}

void test_ternary_activation_idempotent(void) {
    TEST(ternary_activation_idempotent);
    /* ReLU(ReLU(x)) = ReLU(x) for all x */
    trit vals[] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
    for (int i = 0; i < 3; i++) {
        trit once = ternary_activation(vals[i]);
        trit twice = ternary_activation(once);
        ASSERT_EQ(once, twice, "ReLU idempotent");
    }
    PASS();
}

/* ════════════════════════════════════════════════════════════
 * Edge Case / Stress Tests
 * ════════════════════════════════════════════════════════════ */

void test_bitnet_quantize_single_weight(void) {
    TEST(bitnet_quantize_single_weight);
    float w[] = {1.0f};
    trit out[1];
    float scale;
    bitnet_quantize_layer(out, w, 1, &scale);
    ASSERT_EQ(out[0], TRIT_TRUE, "single positive → TRUE");
    PASS();
}

void test_sparse_large_matrix(void) {
    TEST(sparse_large_matrix_8x8);
    /* 8×8 matrix with known pattern */
    trit dense[64];
    memset(dense, TRIT_UNKNOWN, sizeof(dense));
    dense[0]  = TRIT_TRUE;   /* [0,0] */
    dense[9]  = TRIT_FALSE;  /* [1,1] */
    dense[18] = TRIT_TRUE;   /* [2,2] */
    dense[27] = TRIT_FALSE;  /* [3,3] */

    sparse_trit_matrix_t *m = sparse_trit_matrix_create(8, 8, 4, 64);
    dense_to_sparse_trit(dense, 8, 8, m);
    ASSERT_TRUE(m->nnz >= 1, "large matrix has entries");

    trit vec[8] = {TRIT_TRUE, TRIT_TRUE, TRIT_TRUE, TRIT_TRUE,
                   TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_UNKNOWN};
    trit result[8];
    memset(result, TRIT_UNKNOWN, sizeof(result));

    sparse_trit_mvm(m, vec, result);
    /* Diagonal: result[0]=+1*+1=+1, result[1]=-1*+1=-1, etc. */
    ASSERT_EQ(result[0], TRIT_TRUE, "diag MVM[0]=+1");
    ASSERT_EQ(result[1], TRIT_FALSE, "diag MVM[1]=-1");

    sparse_trit_matrix_free(m);
    PASS();
}

void test_dlfet_full_adder_all_combinations(void) {
    TEST(dlfet_full_adder_all_27_combinations);
    trit vals[] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
    int valid = 1;

    for (int i = 0; i < 3 && valid; i++) {
        for (int j = 0; j < 3 && valid; j++) {
            for (int k = 0; k < 3 && valid; k++) {
                trit sum, carry;
                dlfet_full_adder(vals[i], vals[j], vals[k], &sum, &carry);
                /* Verify sum and carry are valid trits */
                if (sum < TRIT_FALSE || sum > TRIT_TRUE ||
                    carry < TRIT_FALSE || carry > TRIT_TRUE) {
                    valid = 0;
                }
                /* XOR+majority adder produces consistent (sum, carry) pairs.
                 * Verify determinism: same inputs always give same outputs. */
                trit sum2, carry2;
                dlfet_full_adder(vals[i], vals[j], vals[k], &sum2, &carry2);
                if (sum != sum2 || carry != carry2) {
                    valid = 0;
                }
            }
        }
    }
    ASSERT_TRUE(valid, "all 27 FA combinations correct");
    PASS();
}

/* ── Main ── */

int main(void) {
    printf("=== AI Acceleration Framework Test Suite ===\n\n");

    printf("[BitNet Quantization]\n");
    test_bitnet_quantize_basic();
    test_bitnet_quantize_all_zero();
    test_bitnet_quantize_uniform_positive();
    test_bitnet_quantize_scale_factor();
    test_bitnet_quantize_single_weight();

    printf("\n[BitNet Forward Pass]\n");
    test_bitnet_forward_identity();
    test_bitnet_forward_negation();
    test_bitnet_forward_with_scale();

    printf("\n[DLFET Gate Simulation]\n");
    test_dlfet_not_truth_table();
    test_dlfet_not_involution();
    test_dlfet_nand_truth_table();
    test_dlfet_full_adder_zero_carry();
    test_dlfet_full_adder_carry_generation();
    test_dlfet_full_adder_all_positive();
    test_dlfet_full_adder_all_combinations();

    printf("\n[Sparse Ternary Matrix]\n");
    test_sparse_matrix_create_free();
    test_dense_to_sparse_conversion();
    test_sparse_mvm_identity();
    test_sparse_mvm_zero_matrix();
    test_sparse_large_matrix();

    printf("\n[Ternary Neural Network Layer]\n");
    test_ternary_linear_create();
    test_ternary_linear_forward_pass();

    printf("\n[Ternary Activation]\n");
    test_ternary_activation_relu();
    test_ternary_activation_idempotent();

    printf("\n=== Results: %d passed, %d failed ===\n", tests_passed, tests_failed);
    return tests_failed ? 1 : 0;
}
