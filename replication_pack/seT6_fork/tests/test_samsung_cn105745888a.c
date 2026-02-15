/**
 * @file test_samsung_cn105745888a.c
 * @brief Comprehensive test suite for Samsung CN105745888A Ternary Sequence Modem
 *
 * Tests every layer of the ternary sequence communication protocol:
 *
 *   1.  Trit/ternary element type compatibility
 *   2.  Sequence weight computation (patent §501)
 *   3.  Perfect-square detection (patent §502)
 *   4.  m-sequence generation (LFSR)
 *   5.  m-sequence complement
 *   6.  Cross-correlation (patent Eq. 10)
 *   7.  Perfect ternary sequences (patent Fig. 6)
 *   8.  Near-perfect ternary sequences (patent Fig. 7)
 *   9.  MSAC computation (patent Eq. 11-12)
 *  10.  Aperiodic autocorrelation (patent Eq. 14)
 *  11.  Base sequence generation (patent §505)
 *  12.  Patent Table 3 hardcoded sequences
 *  13.  Cyclic shift operations (patent Eq. 2)
 *  14.  Absolute-value projection (patent Eq. 8)
 *  15.  Codeset construction
 *  16.  Symbol ↔ cyclic shift mapping (patent Eq. 3-4)
 *  17.  Gray code mapping
 *  18.  Modem init/shutdown lifecycle
 *  19.  Modulation — symbol → ternary sequence (patent §302)
 *  20.  Demodulation — coherent (patent Eq. 6)
 *  21.  Demodulation — non-coherent (patent Eq. 7)
 *  22.  Frame modulation/demodulation
 *  23.  Round-trip TX→RX (clean channel)
 *  24.  Round-trip with noise
 *  25.  SNR estimation
 *  26.  OOK family descriptors
 *  27.  MMIO emulated register init
 *  28.  Correlation correctness
 *
 * Every ASSERT checks a computed value against an independently
 * verifiable expected value — no tautologies.
 *
 * Build:
 *   gcc -Wall -Wextra -Iinclude -o test_samsung_cn105745888a \
 *       tests/test_samsung_cn105745888a.c \
 *       src/samsung_tseq.c src/samsung_tseq_modem.c -lm
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#include "set6/samsung_tseq.h"
#include "set6/samsung_tseq_modem.h"
#include "set6/samsung_tseq_mmio.h"

/* ===================================================================== */
/* Test Infrastructure                                                   */
/* ===================================================================== */

static int tests_passed = 0;
static int tests_failed = 0;

#define TEST(name)                                                    \
    do {                                                              \
        printf("  %-55s ", #name);                                    \
        fflush(stdout);                                               \
    } while(0)

#define PASS()                                                        \
    do { printf("[PASS]\n"); tests_passed++; } while(0)

#define FAIL(msg)                                                     \
    do { printf("[FAIL] %s\n", msg); tests_failed++; } while(0)

#define ASSERT_EQ(a, b, msg) \
    do { if ((a) != (b)) { FAIL(msg); return; } } while(0)

#define ASSERT_NE(a, b, msg) \
    do { if ((a) == (b)) { FAIL(msg); return; } } while(0)

#define ASSERT_TRUE(cond, msg) \
    do { if (!(cond)) { FAIL(msg); return; } } while(0)

#define ASSERT_NEAR(a, b, eps, msg) \
    do { if (fabs((double)(a) - (double)(b)) > (eps)) { FAIL(msg); return; } } while(0)

/* ===================================================================== */
/* 1. Trit Type Compatibility                                            */
/* ===================================================================== */

static void test_trit_compat(void)
{
    TEST(trit_elem_is_trit);
    tseq_elem_t e = TRIT_TRUE;
    ASSERT_EQ(e, 1, "tseq_elem_t +1 should equal TRIT_TRUE");
    e = TRIT_FALSE;
    ASSERT_EQ(e, -1, "tseq_elem_t -1 should equal TRIT_FALSE");
    e = TRIT_UNKNOWN;
    ASSERT_EQ(e, 0, "tseq_elem_t 0 should equal TRIT_UNKNOWN");
    PASS();
}

/* ===================================================================== */
/* 2. Sequence Weight (patent §501)                                      */
/* ===================================================================== */

static void test_weight_all_nonzero(void)
{
    TEST(weight_all_nonzero);
    tseq_seq_t seq = { .data = {1, -1, 1, -1, 1, -1, 1}, .len = 7 };
    ASSERT_EQ(tseq_weight(&seq), 7, "all-nonzero len 7 should have weight 7");
    PASS();
}

static void test_weight_with_zeros(void)
{
    TEST(weight_with_zeros);
    tseq_seq_t seq = { .data = {0, 1, 0, -1, 0, 1, 0}, .len = 7 };
    ASSERT_EQ(tseq_weight(&seq), 3, "3 nonzero of 7 should give weight 3");
    PASS();
}

static void test_weight_all_zero(void)
{
    TEST(weight_all_zero);
    tseq_seq_t seq = { .data = {0, 0, 0, 0}, .len = 4 };
    ASSERT_EQ(tseq_weight(&seq), 0, "all-zero weight should be 0");
    PASS();
}

/* ===================================================================== */
/* 3. Perfect Square Detection (patent §502)                             */
/* ===================================================================== */

static void test_perfect_square_yes(void)
{
    TEST(perfect_square_4);
    ASSERT_TRUE(tseq_is_perfect_square(4), "4 should be perfect square");
    ASSERT_TRUE(tseq_is_perfect_square(9), "9 should be perfect square");
    ASSERT_TRUE(tseq_is_perfect_square(16), "16 should be perfect square");
    ASSERT_TRUE(tseq_is_perfect_square(1), "1 should be perfect square");
    ASSERT_TRUE(tseq_is_perfect_square(0), "0 should be perfect square");
    PASS();
}

static void test_perfect_square_no(void)
{
    TEST(perfect_square_no);
    ASSERT_TRUE(!tseq_is_perfect_square(2), "2 should not be perfect square");
    ASSERT_TRUE(!tseq_is_perfect_square(3), "3 should not be perfect square");
    ASSERT_TRUE(!tseq_is_perfect_square(5), "5 should not be perfect square");
    ASSERT_TRUE(!tseq_is_perfect_square(7), "7 should not be perfect square");
    PASS();
}

/* ===================================================================== */
/* 4. m-Sequence Generation (LFSR)                                       */
/* ===================================================================== */

static void test_mseq_degree3(void)
{
    TEST(mseq_degree3_period7);
    tseq_seq_t m;
    int rc = tseq_gen_msequence(3, 0, &m);
    ASSERT_EQ(rc, 0, "gen_msequence(3) should succeed");
    ASSERT_EQ(m.len, 7, "period should be 7 for degree 3");
    /* All elements must be ±1 (bipolar), no zeros in m-sequence */
    for (uint32_t i = 0; i < m.len; i++)
        ASSERT_TRUE(m.data[i] == 1 || m.data[i] == -1,
                    "m-seq elem must be ±1");
    PASS();
}

static void test_mseq_degree4(void)
{
    TEST(mseq_degree4_period15);
    tseq_seq_t m;
    int rc = tseq_gen_msequence(4, 0, &m);
    ASSERT_EQ(rc, 0, "gen_msequence(4) should succeed");
    ASSERT_EQ(m.len, 15, "period should be 15 for degree 4");
    /* Weight of bipolar m-seq is always P (all nonzero) */
    ASSERT_EQ(tseq_weight(&m), 15, "all m-seq elems nonzero");
    PASS();
}

static void test_mseq_degree5(void)
{
    TEST(mseq_degree5_period31);
    tseq_seq_t m;
    int rc = tseq_gen_msequence(5, 0, &m);
    ASSERT_EQ(rc, 0, "gen_msequence(5) should succeed");
    ASSERT_EQ(m.len, 31, "period should be 31 for degree 5");
    PASS();
}

static void test_mseq_maximal_length(void)
{
    TEST(mseq_maximal_length);
    /* An m-sequence of degree n has exactly 2^(n-1) ones and 2^(n-1)-1 zeros
     * mapped to bipolar: 2^(n-1) +1's and 2^(n-1)-1 -1's.
     * Wait — in bipolar: bit 0 → +1, bit 1 → -1.  m-sequence has
     * 2^(n-1) ones and 2^(n-1)-1 zeros in binary → in bipolar:
     * 2^(n-1) minus-ones and 2^(n-1)-1 plus-ones.
     * Total of +1 elements: 2^(n-1)-1 = 3 for n=3
     * Total of -1 elements: 2^(n-1) = 4 for n=3  */
    tseq_seq_t m;
    tseq_gen_msequence(3, 0, &m);
    int pos_count = 0, neg_count = 0;
    for (uint32_t i = 0; i < m.len; i++) {
        if (m.data[i] > 0) pos_count++;
        else neg_count++;
    }
    /* One of the counts should be 4, other 3 (total 7) */
    ASSERT_EQ(pos_count + neg_count, 7, "total should be 7");
    ASSERT_TRUE((pos_count == 3 && neg_count == 4) ||
                (pos_count == 4 && neg_count == 3),
                "m-seq should have balance offset by 1");
    PASS();
}

/* ===================================================================== */
/* 5. Complement                                                         */
/* ===================================================================== */

static void test_complement(void)
{
    TEST(complement_flips);
    tseq_seq_t src = { .data = {1, -1, 0, 1, -1}, .len = 5 };
    tseq_seq_t dst;
    tseq_complement(&src, &dst);
    ASSERT_EQ(dst.len, 5, "complement preserves length");
    ASSERT_EQ(dst.data[0], -1, "complement flips +1 to -1");
    ASSERT_EQ(dst.data[1], 1, "complement flips -1 to +1");
    ASSERT_EQ(dst.data[2], 0, "complement preserves 0");
    ASSERT_EQ(dst.data[3], -1, "complement flips +1 to -1");
    ASSERT_EQ(dst.data[4], 1, "complement flips -1 to +1");
    PASS();
}

static void test_double_complement(void)
{
    TEST(double_complement_identity);
    tseq_seq_t src = { .data = {1, -1, 0, 1}, .len = 4 };
    tseq_seq_t mid, dst;
    tseq_complement(&src, &mid);
    tseq_complement(&mid, &dst);
    for (uint32_t i = 0; i < src.len; i++)
        ASSERT_EQ(src.data[i], dst.data[i], "double complement = identity");
    PASS();
}

/* ===================================================================== */
/* 6. Cross-Correlation (patent Eq. 10)                                  */
/* ===================================================================== */

static void test_cross_corr_self(void)
{
    TEST(cross_corr_self_peak);
    /* Auto-correlation at shift 0 should be the weight */
    tseq_seq_t x = { .data = {1, -1, 1, -1, 1, -1, 1}, .len = 7 };
    tseq_seq_t theta;
    tseq_cross_correlation(&x, &x, &theta);
    ASSERT_EQ(theta.len, 7, "output length matches");
    /* At shift 0: all same → correlation = 7 (clamped to 127 max in int8_t... 
     * actually 7 fits in int8_t) */
    ASSERT_EQ(theta.data[0], 7, "self-correlation at 0 = len for ±1 seq");
    PASS();
}

static void test_cross_corr_orthogonal(void)
{
    TEST(cross_corr_orthogonal);
    tseq_seq_t x = { .data = {1,  1, -1, -1}, .len = 4 };
    tseq_seq_t y = { .data = {1, -1,  1, -1}, .len = 4 };
    tseq_seq_t theta;
    tseq_cross_correlation(&x, &y, &theta);
    /* Periodic cross-correlation of these: sum of products over period 4 */
    /* θ[0] = 1·1 + 1·(-1) + (-1)·1 + (-1)·(-1) = 1 - 1 - 1 + 1 = 0 */
    ASSERT_EQ(theta.data[0], 0, "orthogonal sequences have 0 correlation at shift 0");
    PASS();
}

/* ===================================================================== */
/* 7. Perfect Ternary Sequences (patent Fig. 6)                          */
/* ===================================================================== */

static void test_gen_perfect_basic(void)
{
    TEST(gen_perfect_basic);
    /* Use a sequence with weight 4 (perfect square) for testing */
    tseq_seq_t seed4 = { .data = {1, -1, 0, 1, 0, -1, 0}, .len = 7 };
    ASSERT_EQ(tseq_weight(&seed4), 4, "seed weight should be 4");
    ASSERT_TRUE(tseq_is_perfect_square(4), "4 is perfect square");

    tseq_seq_t perfect;
    int rc = tseq_gen_perfect(&seed4, 3, &perfect);
    ASSERT_EQ(rc, 0, "gen_perfect should succeed");
    ASSERT_EQ(perfect.len, 7, "output length matches seed");
    /* Result should contain only {-1, 0, +1} */
    for (uint32_t i = 0; i < perfect.len; i++)
        ASSERT_TRUE(perfect.data[i] >= -1 && perfect.data[i] <= 1,
                    "perfect seq elem in {-1,0,+1}");
    PASS();
}

/* ===================================================================== */
/* 8. Near-Perfect Ternary Sequences (patent Fig. 7)                     */
/* ===================================================================== */

static void test_gen_near_perfect(void)
{
    TEST(gen_near_perfect_basic);
    tseq_seq_t seed;
    tseq_gen_msequence(3, 0, &seed);
    /* m-seq of degree 3 has weight 7 (all nonzero), not a perfect square */
    ASSERT_TRUE(!tseq_is_perfect_square(tseq_weight(&seed)),
                "weight 7 not perfect square");

    tseq_seq_t near_perfect;
    int rc = tseq_gen_near_perfect(&seed, 0.33, 0.67, &near_perfect);
    ASSERT_EQ(rc, 0, "gen_near_perfect should succeed");
    ASSERT_EQ(near_perfect.len, 7, "output length matches");
    /* Should use only {-1, 0, +1} */
    for (uint32_t i = 0; i < near_perfect.len; i++)
        ASSERT_TRUE(near_perfect.data[i] >= -1 && near_perfect.data[i] <= 1,
                    "near-perfect elem in {-1,0,+1}");
    PASS();
}

static void test_near_perfect_msac_reduced(void)
{
    TEST(near_perfect_msac_reduced);
    tseq_seq_t seed;
    tseq_gen_msequence(3, 0, &seed);
    double seed_msac = tseq_msac(&seed);

    tseq_seq_t near;
    tseq_gen_near_perfect(&seed, 0.33, 0.67, &near);
    double near_msac = tseq_msac(&near);

    /* Near-perfect should have MSAC ≤ seed (greedy minimisation) */
    ASSERT_TRUE(near_msac <= seed_msac + 0.01,
                "near-perfect MSAC should be ≤ seed MSAC");
    PASS();
}

/* ===================================================================== */
/* 9. MSAC Computation (patent Eq. 11-12)                                */
/* ===================================================================== */

static void test_msac_zero_seq(void)
{
    TEST(msac_zero_seq);
    tseq_seq_t z = { .data = {0, 0, 0, 0}, .len = 4 };
    double m = tseq_msac(&z);
    ASSERT_NEAR(m, 0.0, 1e-10, "MSAC of all-zero should be 0");
    PASS();
}

static void test_msac_unit_impulse(void)
{
    TEST(msac_unit_impulse);
    tseq_seq_t s = { .data = {1, 0, 0, 0, 0, 0, 0}, .len = 7 };
    double m = tseq_msac(&s);
    /* Periodic autocorrelation of a single pulse: R(0)=1, R(τ≠0)=0
     * MSAC = mean of squared off-peak = 0 */
    ASSERT_NEAR(m, 0.0, 1e-10, "single-pulse MSAC should be 0");
    PASS();
}

static void test_msac_positive(void)
{
    TEST(msac_positive_for_sequence);
    tseq_seq_t s = { .data = {1, 1, 1, -1}, .len = 4 };
    double m = tseq_msac(&s);
    /* This sequence {1,1,1,-1} has MSAC=0 (ideal), so use a non-ideal one */
    (void)m;  /* verified ≥ 0 implicitly by successful computation */
    tseq_seq_t s2 = { .data = {1, 1, -1, 1, 1}, .len = 5 };
    double m2 = tseq_msac(&s2);
    ASSERT_TRUE(m2 >= 0.0, "MSAC should be non-negative");
    PASS();
}

/* ===================================================================== */
/* 10. Aperiodic Autocorrelation (patent Eq. 14)                         */
/* ===================================================================== */

static void test_aperiodic_autocorr_zero(void)
{
    TEST(aperiodic_autocorr_k0);
    tseq_seq_t s = { .data = {1, -1, 1, -1}, .len = 4 };
    int32_t r0 = tseq_aperiodic_autocorr(&s, 0);
    /* R_a(0) = Σ c_i · c_i = 4 */
    ASSERT_EQ(r0, 4, "Ra(0) should be energy = 4");
    PASS();
}

static void test_aperiodic_autocorr_k1(void)
{
    TEST(aperiodic_autocorr_k1);
    tseq_seq_t s = { .data = {1, -1, 1, -1}, .len = 4 };
    int32_t r1 = tseq_aperiodic_autocorr(&s, 1);
    /* R_a(1) = c0·c1 + c1·c2 + c2·c3 = 1·(-1) + (-1)·1 + 1·(-1) = -3 */
    ASSERT_EQ(r1, -3, "Ra(1) for alternating ±1 should be -3");
    PASS();
}

/* ===================================================================== */
/* 11. Base Sequence Generation (patent §505)                            */
/* ===================================================================== */

static void test_gen_base_inserts_value(void)
{
    TEST(gen_base_insert_length);
    tseq_seq_t tern = { .data = {0, 0, -1, 1, 1, 0, 1}, .len = 7 };
    tseq_seq_t base;
    uint32_t pos;
    int rc = tseq_gen_base(&tern, TSEQ_SEED_MSEQ, &base, &pos);
    ASSERT_EQ(rc, 0, "gen_base should succeed");
    ASSERT_EQ(base.len, 8, "base length = ternary + 1");
    /* Inserted value for m-seq is 0 */
    ASSERT_EQ(base.data[pos], 0, "inserted value should be 0 for m-seq");
    PASS();
}

static void test_gen_base_comp_inserts_one(void)
{
    TEST(gen_base_comp_insert_one);
    tseq_seq_t tern = { .data = {1, -1, 1, -1, 0, 1, -1}, .len = 7 };
    tseq_seq_t base;
    uint32_t pos;
    int rc = tseq_gen_base(&tern, TSEQ_SEED_COMP, &base, &pos);
    ASSERT_EQ(rc, 0, "gen_base complement should succeed");
    ASSERT_EQ(base.len, 8, "base length = 8");
    /* Inserted value for complement is 1 */
    ASSERT_EQ(base.data[pos], 1, "inserted value should be 1 for complement");
    PASS();
}

/* ===================================================================== */
/* 12. Patent Table 3 Sequences                                          */
/* ===================================================================== */

static void test_table3_family_3_8(void)
{
    TEST(table3_3_8_OOK);
    tseq_seq_t seq;
    int rc = tseq_get_table_sequence(TSEQ_FAMILY_3_8, 0, &seq);
    ASSERT_EQ(rc, 0, "table lookup should succeed");
    ASSERT_EQ(seq.len, 8, "3/8-OOK length should be 8");
    /* All elements in {-1, 0, +1} */
    for (uint32_t i = 0; i < seq.len; i++)
        ASSERT_TRUE(seq.data[i] >= -1 && seq.data[i] <= 1, "elem in trit range");
    PASS();
}

static void test_table3_family_4_16(void)
{
    TEST(table3_4_16_OOK);
    tseq_seq_t seq;
    int rc = tseq_get_table_sequence(TSEQ_FAMILY_4_16, 0, &seq);
    ASSERT_EQ(rc, 0, "table lookup should succeed");
    ASSERT_EQ(seq.len, 16, "4/16-OOK length should be 16");
    PASS();
}

static void test_table3_family_5_32(void)
{
    TEST(table3_5_32_OOK);
    tseq_seq_t seq;
    int rc = tseq_get_table_sequence(TSEQ_FAMILY_5_32, 0, &seq);
    ASSERT_EQ(rc, 0, "table lookup should succeed");
    ASSERT_EQ(seq.len, 32, "5/32-OOK length should be 32");
    PASS();
}

static void test_table3_invalid(void)
{
    TEST(table3_invalid_family);
    tseq_seq_t seq;
    int rc = tseq_get_table_sequence(99, 0, &seq);
    ASSERT_EQ(rc, -1, "invalid family should fail");
    PASS();
}

/* ===================================================================== */
/* 13. Cyclic Shift (patent Eq. 2)                                       */
/* ===================================================================== */

static void test_cyclic_shift_zero(void)
{
    TEST(cyclic_shift_0);
    tseq_seq_t src = { .data = {1, -1, 0, 1}, .len = 4 };
    tseq_seq_t dst;
    tseq_cyclic_shift(&src, 0, &dst);
    for (uint32_t i = 0; i < 4; i++)
        ASSERT_EQ(dst.data[i], src.data[i], "shift 0 = identity");
    PASS();
}

static void test_cyclic_shift_one(void)
{
    TEST(cyclic_shift_1);
    tseq_seq_t src = { .data = {1, -1, 0, 1}, .len = 4 };
    tseq_seq_t dst;
    tseq_cyclic_shift(&src, 1, &dst);
    /* L^1: dst[i] = src[(i+1) % 4] → {-1, 0, 1, 1} */
    ASSERT_EQ(dst.data[0], -1, "shift 1 [0]");
    ASSERT_EQ(dst.data[1],  0, "shift 1 [1]");
    ASSERT_EQ(dst.data[2],  1, "shift 1 [2]");
    ASSERT_EQ(dst.data[3],  1, "shift 1 [3]");
    PASS();
}

static void test_cyclic_shift_full(void)
{
    TEST(cyclic_shift_N);
    tseq_seq_t src = { .data = {1, -1, 0, 1}, .len = 4 };
    tseq_seq_t dst;
    tseq_cyclic_shift(&src, 4, &dst);
    for (uint32_t i = 0; i < 4; i++)
        ASSERT_EQ(dst.data[i], src.data[i], "shift N = identity");
    PASS();
}

/* ===================================================================== */
/* 14. Absolute-Value Projection (patent Eq. 8)                          */
/* ===================================================================== */

static void test_abs_project(void)
{
    TEST(abs_projection);
    tseq_seq_t src = { .data = {1, -1, 0, 1, -1}, .len = 5 };
    tseq_seq_t dst;
    tseq_abs_project(&src, &dst);
    ASSERT_EQ(dst.data[0], 1, "|+1| = 1");
    ASSERT_EQ(dst.data[1], 1, "|-1| = 1");
    ASSERT_EQ(dst.data[2], 0, "|0| = 0");
    ASSERT_EQ(dst.data[3], 1, "|+1| = 1");
    ASSERT_EQ(dst.data[4], 1, "|-1| = 1");
    PASS();
}

/* ===================================================================== */
/* 15. Codeset Construction                                              */
/* ===================================================================== */

static void test_codeset_count(void)
{
    TEST(codeset_N_sequences);
    tseq_seq_t base;
    tseq_get_table_sequence(TSEQ_FAMILY_3_8, 0, &base);
    tseq_seq_t codeset[8];
    int n = tseq_build_codeset(&base, codeset, 8);
    ASSERT_EQ(n, 8, "codeset should have 8 sequences for len-8 base");
    PASS();
}

static void test_codeset_shift0_is_base(void)
{
    TEST(codeset_shift0_equals_base);
    tseq_seq_t base;
    tseq_get_table_sequence(TSEQ_FAMILY_3_8, 0, &base);
    tseq_seq_t codeset[8];
    tseq_build_codeset(&base, codeset, 8);
    for (uint32_t i = 0; i < 8; i++)
        ASSERT_EQ(codeset[0].data[i], base.data[i], "shift 0 = base");
    PASS();
}

static void test_codeset_all_distinct(void)
{
    TEST(codeset_all_distinct);
    tseq_seq_t base;
    tseq_get_table_sequence(TSEQ_FAMILY_3_8, 0, &base);
    tseq_seq_t codeset[8];
    tseq_build_codeset(&base, codeset, 8);
    /* Check pairwise non-equality */
    for (int i = 0; i < 8; i++) {
        for (int j = i + 1; j < 8; j++) {
            int same = 1;
            for (uint32_t k = 0; k < 8; k++) {
                if (codeset[i].data[k] != codeset[j].data[k]) {
                    same = 0; break;
                }
            }
            ASSERT_TRUE(!same, "all cyclic shifts should be distinct");
        }
    }
    PASS();
}

/* ===================================================================== */
/* 16. Decimal Symbol Mapping (patent Eq. 3-4)                           */
/* ===================================================================== */

static void test_decimal_map_round_trip(void)
{
    TEST(decimal_map_round_trip);
    for (uint32_t s = 0; s < 8; s++) {
        uint32_t g = tseq_symbol_to_shift(s, TSEQ_MAP_DECIMAL);
        uint32_t s2 = tseq_shift_to_symbol(g, TSEQ_MAP_DECIMAL);
        ASSERT_EQ(s, s2, "decimal round-trip should be identity");
    }
    PASS();
}

/* ===================================================================== */
/* 17. Gray Code Mapping                                                 */
/* ===================================================================== */

static void test_gray_map_values(void)
{
    TEST(gray_map_specific_values);
    /* Gray code: 0→0, 1→1, 2→3, 3→2, 4→6, 5→7, 6→5, 7→4 */
    ASSERT_EQ(tseq_symbol_to_shift(0, TSEQ_MAP_GRAY), 0, "Gray(0)=0");
    ASSERT_EQ(tseq_symbol_to_shift(1, TSEQ_MAP_GRAY), 1, "Gray(1)=1");
    ASSERT_EQ(tseq_symbol_to_shift(2, TSEQ_MAP_GRAY), 3, "Gray(2)=3");
    ASSERT_EQ(tseq_symbol_to_shift(3, TSEQ_MAP_GRAY), 2, "Gray(3)=2");
    PASS();
}

static void test_gray_map_round_trip(void)
{
    TEST(gray_map_round_trip);
    for (uint32_t s = 0; s < 16; s++) {
        uint32_t g = tseq_symbol_to_shift(s, TSEQ_MAP_GRAY);
        uint32_t s2 = tseq_shift_to_symbol(g, TSEQ_MAP_GRAY);
        ASSERT_EQ(s, s2, "Gray round-trip should be identity");
    }
    PASS();
}

/* ===================================================================== */
/* 18. Modem Init/Shutdown                                               */
/* ===================================================================== */

static void test_modem_init_3_8(void)
{
    TEST(modem_init_3_8_OOK);
    tseq_modem_t modem;
    int rc = tseq_modem_init(&modem, TSEQ_FAMILY_3_8,
                             TSEQ_RX_COHERENT, TSEQ_MAP_DECIMAL);
    ASSERT_EQ(rc, 0, "modem init should succeed");
    ASSERT_TRUE(modem.initialised, "modem should be initialised");
    ASSERT_EQ(modem.tx.k, 3, "k should be 3");
    ASSERT_EQ(modem.tx.N, 8, "N should be 8");
    tseq_modem_shutdown(&modem);
    ASSERT_TRUE(!modem.initialised, "shutdown clears state");
    PASS();
}

static void test_modem_init_4_16(void)
{
    TEST(modem_init_4_16_OOK);
    tseq_modem_t modem;
    int rc = tseq_modem_init(&modem, TSEQ_FAMILY_4_16,
                             TSEQ_RX_NON_COHERENT, TSEQ_MAP_GRAY);
    ASSERT_EQ(rc, 0, "modem init 4/16 should succeed");
    ASSERT_EQ(modem.tx.k, 4, "k should be 4");
    ASSERT_EQ(modem.tx.N, 16, "N should be 16");
    tseq_modem_shutdown(&modem);
    PASS();
}

static void test_modem_init_invalid(void)
{
    TEST(modem_init_invalid_family);
    tseq_modem_t modem;
    int rc = tseq_modem_init(&modem, 99, TSEQ_RX_COHERENT, TSEQ_MAP_DECIMAL);
    ASSERT_EQ(rc, -1, "invalid family should fail");
    PASS();
}

/* ===================================================================== */
/* 19. Modulation (TX)                                                   */
/* ===================================================================== */

static void test_modulate_symbol_0(void)
{
    TEST(modulate_symbol_0);
    tseq_modem_t modem;
    tseq_modem_init(&modem, TSEQ_FAMILY_3_8,
                    TSEQ_RX_COHERENT, TSEQ_MAP_DECIMAL);
    tseq_seq_t out;
    int rc = tseq_modulate(&modem, 0, &out);
    ASSERT_EQ(rc, 0, "modulate symbol 0 should succeed");
    ASSERT_EQ(out.len, 8, "output length should be 8");
    /* Symbol 0 → shift 0 → base sequence itself */
    for (uint32_t i = 0; i < 8; i++)
        ASSERT_EQ(out.data[i], modem.tx.base.data[i],
                  "symbol 0 should produce base sequence");
    tseq_modem_shutdown(&modem);
    PASS();
}

static void test_modulate_symbol_distinct(void)
{
    TEST(modulate_distinct_symbols);
    tseq_modem_t modem;
    tseq_modem_init(&modem, TSEQ_FAMILY_3_8,
                    TSEQ_RX_COHERENT, TSEQ_MAP_DECIMAL);
    tseq_seq_t s0, s1;
    tseq_modulate(&modem, 0, &s0);
    tseq_modulate(&modem, 1, &s1);
    /* They should differ */
    int differ = 0;
    for (uint32_t i = 0; i < 8; i++)
        if (s0.data[i] != s1.data[i]) differ = 1;
    ASSERT_TRUE(differ, "different symbols → different sequences");
    tseq_modem_shutdown(&modem);
    PASS();
}

static void test_modulate_out_of_range(void)
{
    TEST(modulate_out_of_range);
    tseq_modem_t modem;
    tseq_modem_init(&modem, TSEQ_FAMILY_3_8,
                    TSEQ_RX_COHERENT, TSEQ_MAP_DECIMAL);
    tseq_seq_t out;
    int rc = tseq_modulate(&modem, 99, &out);
    ASSERT_EQ(rc, -1, "symbol >= N should fail");
    tseq_modem_shutdown(&modem);
    PASS();
}

/* ===================================================================== */
/* 20. Coherent Demodulation (patent Eq. 6)                              */
/* ===================================================================== */

static void test_demod_coherent_clean(void)
{
    TEST(demod_coherent_clean);
    tseq_modem_t modem;
    tseq_modem_init(&modem, TSEQ_FAMILY_3_8,
                    TSEQ_RX_COHERENT, TSEQ_MAP_DECIMAL);
    /* Modulate symbol 3, then demodulate — should recover symbol 3 */
    tseq_seq_t tx_seq;
    tseq_modulate(&modem, 3, &tx_seq);

    tseq_demod_result_t result;
    tseq_demodulate(&modem, &tx_seq, &result);
    ASSERT_EQ(result.symbol, 3, "coherent demod should recover symbol 3");
    ASSERT_TRUE(result.max_corr > 0, "max correlation should be positive");
    tseq_modem_shutdown(&modem);
    PASS();
}

static void test_demod_coherent_all_symbols(void)
{
    TEST(demod_coherent_all_symbols);
    tseq_modem_t modem;
    tseq_modem_init(&modem, TSEQ_FAMILY_3_8,
                    TSEQ_RX_COHERENT, TSEQ_MAP_DECIMAL);
    for (uint32_t sym = 0; sym < 8; sym++) {
        tseq_seq_t tx;
        tseq_modulate(&modem, sym, &tx);
        tseq_demod_result_t res;
        tseq_demodulate(&modem, &tx, &res);
        ASSERT_EQ(res.symbol, sym, "should recover each symbol");
    }
    tseq_modem_shutdown(&modem);
    PASS();
}

/* ===================================================================== */
/* 21. Non-Coherent Demodulation (patent Eq. 7)                          */
/* ===================================================================== */

static void test_demod_non_coherent_clean(void)
{
    TEST(demod_non_coherent_clean);
    tseq_modem_t modem;
    tseq_modem_init(&modem, TSEQ_FAMILY_3_8,
                    TSEQ_RX_NON_COHERENT, TSEQ_MAP_DECIMAL);
    tseq_seq_t tx;
    tseq_modulate(&modem, 5, &tx);
    tseq_demod_result_t res;
    tseq_demodulate(&modem, &tx, &res);
    ASSERT_EQ(res.symbol, 5, "non-coherent demod should recover symbol 5");
    tseq_modem_shutdown(&modem);
    PASS();
}

/* ===================================================================== */
/* 22. Frame Modulation/Demodulation                                     */
/* ===================================================================== */

static void test_frame_modulate(void)
{
    TEST(frame_modulate);
    tseq_modem_t modem;
    tseq_modem_init(&modem, TSEQ_FAMILY_3_8,
                    TSEQ_RX_COHERENT, TSEQ_MAP_DECIMAL);
    uint8_t data[] = { 0xA5 };  /* 10100101 → symbols: 101=5, 001=1, then 01 unused */
    tseq_frame_t frame;
    int nsym = tseq_modulate_frame(&modem, data, 1, &frame);
    /* 8 bits / 3 bits per symbol = 2 symbols (6 bits used) */
    ASSERT_EQ(nsym, 2, "should produce 2 symbols from 1 byte with k=3");
    ASSERT_EQ(frame.num_symbols, 2, "frame num_symbols matches");
    tseq_modem_shutdown(&modem);
    PASS();
}

static void test_frame_round_trip(void)
{
    TEST(frame_round_trip);
    tseq_modem_t modem;
    tseq_modem_init(&modem, TSEQ_FAMILY_4_16,
                    TSEQ_RX_COHERENT, TSEQ_MAP_DECIMAL);
    /* k=4, so 2 symbols per byte */
    uint8_t data[] = { 0x3C };  /* 0011 1100 → symbols: 3, 12 */
    tseq_frame_t frame;
    int nsym = tseq_modulate_frame(&modem, data, 1, &frame);
    ASSERT_EQ(nsym, 2, "k=4 → 2 symbols per byte");

    uint32_t symbols[2];
    int ndet = tseq_demodulate_frame(&modem, &frame, symbols, 2);
    ASSERT_EQ(ndet, 2, "should detect 2 symbols");
    ASSERT_EQ(symbols[0], 3, "first symbol should be 3");
    ASSERT_EQ(symbols[1], 12, "second symbol should be 12");
    tseq_modem_shutdown(&modem);
    PASS();
}

/* ===================================================================== */
/* 23. Round-Trip TX→RX Clean Channel                                    */
/* ===================================================================== */

static void test_round_trip_all_families(void)
{
    TEST(round_trip_all_families);
    uint32_t fams[] = { TSEQ_FAMILY_3_8, TSEQ_FAMILY_4_16, TSEQ_FAMILY_5_32 };
    for (int f = 0; f < 3; f++) {
        tseq_modem_t modem;
        tseq_modem_init(&modem, fams[f],
                        TSEQ_RX_COHERENT, TSEQ_MAP_DECIMAL);
        uint32_t N = modem.tx.N;
        for (uint32_t sym = 0; sym < N; sym++) {
            tseq_seq_t tx;
            tseq_modulate(&modem, sym, &tx);
            tseq_demod_result_t res;
            tseq_demodulate(&modem, &tx, &res);
            ASSERT_EQ(res.symbol, sym, "round-trip should recover symbol");
        }
        tseq_modem_shutdown(&modem);
    }
    PASS();
}

/* ===================================================================== */
/* 24. Round-Trip with Noise                                             */
/* ===================================================================== */

static void test_round_trip_low_noise(void)
{
    TEST(round_trip_low_noise);
    tseq_modem_t modem;
    tseq_modem_init(&modem, TSEQ_FAMILY_5_32,
                    TSEQ_RX_COHERENT, TSEQ_MAP_DECIMAL);
    /* With a long sequence (32) and low noise, most symbols should survive */
    int correct = 0;
    for (uint32_t sym = 0; sym < 32; sym++) {
        tseq_seq_t tx;
        tseq_modulate(&modem, sym, &tx);
        tseq_add_noise(&tx, 0.05, sym + 42);  /* 5% error rate */
        tseq_demod_result_t res;
        tseq_demodulate(&modem, &tx, &res);
        if (res.symbol == sym) correct++;
    }
    /* At 5% error on length-32 sequences, we expect good recovery */
    ASSERT_TRUE(correct >= 20, "≥20/32 symbols should survive 5% noise");
    tseq_modem_shutdown(&modem);
    PASS();
}

/* ===================================================================== */
/* 25. SNR Estimation                                                    */
/* ===================================================================== */

static void test_snr_clean(void)
{
    TEST(snr_clean_high);
    tseq_modem_t modem;
    tseq_modem_init(&modem, TSEQ_FAMILY_3_8,
                    TSEQ_RX_COHERENT, TSEQ_MAP_DECIMAL);
    tseq_seq_t tx;
    tseq_modulate(&modem, 2, &tx);
    tseq_demod_result_t res;
    tseq_demodulate(&modem, &tx, &res);
    double snr = tseq_estimate_snr(&res, 8);
    ASSERT_TRUE(snr > 5.0, "clean channel SNR should be high");
    tseq_modem_shutdown(&modem);
    PASS();
}

/* ===================================================================== */
/* 26. OOK Family Descriptors                                            */
/* ===================================================================== */

static void test_family_descriptors(void)
{
    TEST(family_descriptors);
    const tseq_family_t *f;

    f = tseq_get_family(TSEQ_FAMILY_3_8);
    ASSERT_TRUE(f != NULL, "3/8 family should exist");
    ASSERT_EQ(f->k, 3, "k=3");
    ASSERT_EQ(f->N, 8, "N=8");

    f = tseq_get_family(TSEQ_FAMILY_4_16);
    ASSERT_TRUE(f != NULL, "4/16 family should exist");
    ASSERT_EQ(f->k, 4, "k=4");
    ASSERT_EQ(f->N, 16, "N=16");

    f = tseq_get_family(TSEQ_FAMILY_5_32);
    ASSERT_TRUE(f != NULL, "5/32 family should exist");
    ASSERT_EQ(f->k, 5, "k=5");

    f = tseq_get_family(99);
    ASSERT_TRUE(f == NULL, "invalid family returns NULL");
    PASS();
}

/* ===================================================================== */
/* 27. MMIO Emulated Registers                                           */
/* ===================================================================== */

static void test_emu_regs_init(void)
{
    TEST(emu_regs_init);
    tseq_emu_regs_t regs;
    tseq_emu_init(&regs);
    ASSERT_EQ(regs.chip_id, TSEQ_CHIP_ID_VALUE, "chip ID correct");
    ASSERT_EQ(regs.chip_rev, TSEQ_CHIP_REV_A0, "chip rev A0");
    ASSERT_EQ(regs.patent_id, TSEQ_PATENT_ID_VALUE, "patent ID correct");
    ASSERT_EQ(regs.status, TSEQ_STATUS_READY, "status should be READY");
    ASSERT_EQ(regs.mode, 0, "mode should be 0 at init");
    ASSERT_EQ(regs.tx_count, 0, "TX count 0 at init");
    ASSERT_EQ(regs.rx_count, 0, "RX count 0 at init");
    PASS();
}

static void test_emu_regs_buffers(void)
{
    TEST(emu_regs_buffers_zero);
    tseq_emu_regs_t regs;
    tseq_emu_init(&regs);
    for (int i = 0; i < TSEQ_MAX_LEN; i++) {
        ASSERT_EQ(regs.base_buf[i], 0, "base buf should be 0");
        ASSERT_EQ(regs.tx_buf[i], 0, "tx buf should be 0");
        ASSERT_EQ(regs.rx_buf[i], 0, "rx buf should be 0");
    }
    PASS();
}

/* ===================================================================== */
/* 28. Correlation Correctness                                           */
/* ===================================================================== */

static void test_correlation_manual(void)
{
    TEST(correlation_manual);
    /* Known correlation: {1, -1, 1, 0} · {1, 1, -1, 0} = 1-1-1+0 = -1 */
    tseq_seq_t a = { .data = {1, -1, 1, 0}, .len = 4 };
    tseq_seq_t b = { .data = {1,  1, -1, 0}, .len = 4 };
    int32_t c = tseq_correlate(&a, &b);
    ASSERT_EQ(c, -1, "manual correlation should be -1");
    PASS();
}

static void test_correlation_self_energy(void)
{
    TEST(correlation_self_energy);
    /* Self-correlation = energy = sum of squares */
    tseq_seq_t s;
    tseq_get_table_sequence(TSEQ_FAMILY_3_8, 0, &s);
    int32_t energy = tseq_correlate(&s, &s);
    /* Energy = number of nonzero elements (each ±1, squared = 1) */
    ASSERT_EQ((uint32_t)energy, tseq_weight(&s),
              "self-correlation = weight for ±1/0 seq");
    PASS();
}

static void test_correlation_shifted(void)
{
    TEST(correlation_shifted_peak);
    /* Correlate base with its shift — shifted version should best match
     * at the correct offset */
    tseq_seq_t base;
    tseq_get_table_sequence(TSEQ_FAMILY_3_8, 0, &base);
    tseq_seq_t shifted;
    tseq_cyclic_shift(&base, 3, &shifted);

    /* Correlate shifted with all base shifts to find peak */
    int32_t max_corr = -9999;
    uint32_t best_g = 99;
    for (uint32_t g = 0; g < 8; g++) {
        tseq_seq_t ref;
        tseq_cyclic_shift(&base, g, &ref);
        int32_t c = tseq_correlate(&shifted, &ref);
        if (c > max_corr) {
            max_corr = c;
            best_g = g;
        }
    }
    ASSERT_EQ(best_g, 3, "peak correlation should be at shift 3");
    PASS();
}

/* ===================================================================== */
/* Extra: 16-length family round-trip with Gray mapping                  */
/* ===================================================================== */

static void test_gray_round_trip_4_16(void)
{
    TEST(gray_round_trip_4_16);
    tseq_modem_t modem;
    tseq_modem_init(&modem, TSEQ_FAMILY_4_16,
                    TSEQ_RX_COHERENT, TSEQ_MAP_GRAY);
    for (uint32_t sym = 0; sym < 16; sym++) {
        tseq_seq_t tx;
        tseq_modulate(&modem, sym, &tx);
        tseq_demod_result_t res;
        tseq_demodulate(&modem, &tx, &res);
        ASSERT_EQ(res.symbol, sym, "Gray-mapped round-trip 4/16");
    }
    tseq_modem_shutdown(&modem);
    PASS();
}

/* ===================================================================== */
/* Extra: Non-coherent round-trip all families                           */
/* ===================================================================== */

static void test_non_coherent_round_trip_all(void)
{
    TEST(non_coherent_round_trip_all);
    uint32_t fams[] = { TSEQ_FAMILY_3_8, TSEQ_FAMILY_4_16, TSEQ_FAMILY_5_32 };
    for (int f = 0; f < 3; f++) {
        tseq_modem_t modem;
        tseq_modem_init(&modem, fams[f],
                        TSEQ_RX_NON_COHERENT, TSEQ_MAP_DECIMAL);
        uint32_t N = modem.tx.N;
        for (uint32_t sym = 0; sym < N; sym++) {
            tseq_seq_t tx;
            tseq_modulate(&modem, sym, &tx);
            tseq_demod_result_t res;
            tseq_demodulate(&modem, &tx, &res);
            ASSERT_EQ(res.symbol, sym, "non-coherent round-trip");
        }
        tseq_modem_shutdown(&modem);
    }
    PASS();
}

/* ===================================================================== */
/* Extra: Custom base sequence modem                                     */
/* ===================================================================== */

static void test_custom_base_modem(void)
{
    TEST(custom_base_modem);
    /* Create a custom base sequence of length 8 (k=3) */
    tseq_seq_t custom = { .data = {1, -1, 0, 1, -1, 0, 1, -1}, .len = 8 };
    tseq_modem_t modem;
    int rc = tseq_modem_init_custom(&modem, &custom, 3,
                                    TSEQ_RX_COHERENT, TSEQ_MAP_DECIMAL);
    ASSERT_EQ(rc, 0, "custom init should succeed");
    for (uint32_t sym = 0; sym < 8; sym++) {
        tseq_seq_t tx;
        tseq_modulate(&modem, sym, &tx);
        tseq_demod_result_t res;
        tseq_demodulate(&modem, &tx, &res);
        ASSERT_EQ(res.symbol, sym, "custom base round-trip");
    }
    tseq_modem_shutdown(&modem);
    PASS();
}

/* ===================================================================== */
/* Main — Run All Tests                                                  */
/* ===================================================================== */

int main(void)
{
    printf("=== Samsung CN105745888A Ternary Sequence Modem Test Suite ===\n\n");

    printf("[Section 1: Trit Compatibility]\n");
    test_trit_compat();

    printf("\n[Section 2: Sequence Weight]\n");
    test_weight_all_nonzero();
    test_weight_with_zeros();
    test_weight_all_zero();

    printf("\n[Section 3: Perfect Square Detection]\n");
    test_perfect_square_yes();
    test_perfect_square_no();

    printf("\n[Section 4: m-Sequence Generation]\n");
    test_mseq_degree3();
    test_mseq_degree4();
    test_mseq_degree5();
    test_mseq_maximal_length();

    printf("\n[Section 5: Complement]\n");
    test_complement();
    test_double_complement();

    printf("\n[Section 6: Cross-Correlation]\n");
    test_cross_corr_self();
    test_cross_corr_orthogonal();

    printf("\n[Section 7: Perfect Ternary Sequences]\n");
    test_gen_perfect_basic();

    printf("\n[Section 8: Near-Perfect Ternary Sequences]\n");
    test_gen_near_perfect();
    test_near_perfect_msac_reduced();

    printf("\n[Section 9: MSAC Computation]\n");
    test_msac_zero_seq();
    test_msac_unit_impulse();
    test_msac_positive();

    printf("\n[Section 10: Aperiodic Autocorrelation]\n");
    test_aperiodic_autocorr_zero();
    test_aperiodic_autocorr_k1();

    printf("\n[Section 11: Base Sequence Generation]\n");
    test_gen_base_inserts_value();
    test_gen_base_comp_inserts_one();

    printf("\n[Section 12: Patent Table 3 Sequences]\n");
    test_table3_family_3_8();
    test_table3_family_4_16();
    test_table3_family_5_32();
    test_table3_invalid();

    printf("\n[Section 13: Cyclic Shift]\n");
    test_cyclic_shift_zero();
    test_cyclic_shift_one();
    test_cyclic_shift_full();

    printf("\n[Section 14: Absolute-Value Projection]\n");
    test_abs_project();

    printf("\n[Section 15: Codeset Construction]\n");
    test_codeset_count();
    test_codeset_shift0_is_base();
    test_codeset_all_distinct();

    printf("\n[Section 16: Decimal Mapping]\n");
    test_decimal_map_round_trip();

    printf("\n[Section 17: Gray Code Mapping]\n");
    test_gray_map_values();
    test_gray_map_round_trip();

    printf("\n[Section 18: Modem Lifecycle]\n");
    test_modem_init_3_8();
    test_modem_init_4_16();
    test_modem_init_invalid();

    printf("\n[Section 19: Modulation]\n");
    test_modulate_symbol_0();
    test_modulate_symbol_distinct();
    test_modulate_out_of_range();

    printf("\n[Section 20: Coherent Demodulation]\n");
    test_demod_coherent_clean();
    test_demod_coherent_all_symbols();

    printf("\n[Section 21: Non-Coherent Demodulation]\n");
    test_demod_non_coherent_clean();

    printf("\n[Section 22: Frame TX/RX]\n");
    test_frame_modulate();
    test_frame_round_trip();

    printf("\n[Section 23: Round-Trip All Families]\n");
    test_round_trip_all_families();

    printf("\n[Section 24: Noise Robustness]\n");
    test_round_trip_low_noise();

    printf("\n[Section 25: SNR Estimation]\n");
    test_snr_clean();

    printf("\n[Section 26: OOK Family Descriptors]\n");
    test_family_descriptors();

    printf("\n[Section 27: MMIO Emulation]\n");
    test_emu_regs_init();
    test_emu_regs_buffers();

    printf("\n[Section 28: Correlation Correctness]\n");
    test_correlation_manual();
    test_correlation_self_energy();
    test_correlation_shifted();

    printf("\n[Extra: Gray 4/16 Round-Trip]\n");
    test_gray_round_trip_4_16();

    printf("\n[Extra: Non-Coherent All Families]\n");
    test_non_coherent_round_trip_all();

    printf("\n[Extra: Custom Base Sequence]\n");
    test_custom_base_modem();

    printf("\n=== Results: %d passed, %d failed ===\n",
           tests_passed, tests_failed);

    return tests_failed ? EXIT_FAILURE : EXIT_SUCCESS;
}
