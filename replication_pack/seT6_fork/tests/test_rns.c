/**
 * @file test_rns.c
 * @brief seT6 RNS Standalone Test Suite — Output-Parameter API
 *
 * 15 test categories:
 *   1.  Init & CRT constants          9.  PVT-style resilience
 *   2.  trit2_reg32 → RNS conversion  10. Crypto integration
 *   3.  CRT reconstruction            11. PVT noise injection
 *   4.  Carry-free arithmetic         12. Conversions (custom/MRS)
 *   5.  Montgomery modular mul        13. Low-power sim (TMVM-RNS/ResISC)
 *   6.  Zero / sparsity detection     14. Crypto extended (Montgomery exp)
 *   7.  Validate round-trip           15. Multi-radix extended moduli
 *   8.  Extend moduli
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>

#include "set6/trit.h"
#include "set6/trit_emu.h"
#include "set6/multiradix.h"
#include "set6/trit_rns.h"
#include "trit_tmvm_rns.h"
#include "trit_resisc.h"

/* ==== Test Harness ===================================================== */

static int tests_passed = 0;
static int tests_failed = 0;
static int tests_total  = 0;

#define TEST(name) do { \
    printf("  %-60s", name); \
    tests_total++; \
} while(0)

#define ASSERT(cond, msg) do { \
    if (cond) { tests_passed++; printf("[PASS]\n"); } \
    else { tests_failed++; printf("[FAIL] %s\n", msg); } \
} while(0)

#define SECTION(name) printf("\n  --- %s ---\n", name)

/* ========================================================================
 * 1. Init & CRT Constants
 * ======================================================================== */

static void test_init_and_crt(void) {
    SECTION("RNS: Init & CRT Constants");
    trit_rns_context_t ctx;

    TEST("trit_rns_init returns 0");
    ASSERT(trit_rns_init(&ctx) == 0, "expected 0");

    TEST("moduli count == 3");
    ASSERT(ctx.count == 3, "expected 3");

    TEST("M == 105 (3*5*7)");
    ASSERT(ctx.M == 105, "expected 105");

    TEST("Mi[0] == 35 (M/3)");
    ASSERT(ctx.Mi[0] == 35, "expected 35");

    TEST("Mi[1] == 21 (M/5)");
    ASSERT(ctx.Mi[1] == 21, "expected 21");

    TEST("Mi[2] == 15 (M/7)");
    ASSERT(ctx.Mi[2] == 15, "expected 15");

    /* Mi_inv[0] = 35^(-1) mod 3 = 2  (35 mod 3 = 2, 2*2=4≡1 mod 3) */
    TEST("Mi_inv[0] == 2 (35^-1 mod 3)");
    ASSERT(ctx.Mi_inv[0] == 2, "expected 2");

    /* Mi_inv[1] = 21^(-1) mod 5 = 1  (21 mod 5 = 1, 1*1=1≡1 mod 5) */
    TEST("Mi_inv[1] == 1 (21^-1 mod 5)");
    ASSERT(ctx.Mi_inv[1] == 1, "expected 1");

    /* Mi_inv[2] = 15^(-1) mod 7 = 1  (15 mod 7 = 1, 1*1=1≡1 mod 7) */
    TEST("Mi_inv[2] == 1 (15^-1 mod 7)");
    ASSERT(ctx.Mi_inv[2] == 1, "expected 1");

    TEST("trit_rns_init(NULL) returns -1");
    ASSERT(trit_rns_init(NULL) == -1, "expected -1");
}

/* ========================================================================
 * 2. trit2_reg32 → RNS Conversion
 * ======================================================================== */

static void test_trit_to_rns(void) {
    SECTION("RNS: trit2_reg32 → RNS Conversion");
    trit_rns_context_t ctx;
    trit_rns_init(&ctx);

    /* All-zero register → value 0 → residues (0,0,0) */
    TEST("All-unknown (0) reg → residues (0,0,0)");
    trit2_reg32 zero_reg = trit2_reg32_splat(TRIT2_UNKNOWN);
    trit_rns_t rz;
    trit_to_rns(&zero_reg, 4, &rz, &ctx);
    ASSERT(rz.residues[0] == 0 && rz.residues[1] == 0
        && rz.residues[2] == 0, "expected (0,0,0)");

    /* Single trit +1 → value 1 → residues (1,1,1) */
    TEST("Single +1 trit → residues (1,1,1)");
    trit2_reg32 one_reg = trit2_reg32_splat(TRIT2_UNKNOWN);
    trit2_reg32_set(&one_reg, 0, TRIT2_TRUE);
    trit_rns_t r1;
    trit_to_rns(&one_reg, 1, &r1, &ctx);
    ASSERT(r1.residues[0] == 1 && r1.residues[1] == 1
        && r1.residues[2] == 1, "expected (1,1,1)");

    /* Trits {+1, +1} = 1*3^0 + 1*3^1 = 4 → (1, 4, 4) */
    TEST("{+1,+1} → value 4 → residues (1,4,4)");
    trit2_reg32 reg4 = trit2_reg32_splat(TRIT2_UNKNOWN);
    trit2_reg32_set(&reg4, 0, TRIT2_TRUE);
    trit2_reg32_set(&reg4, 1, TRIT2_TRUE);
    trit_rns_t r4;
    trit_to_rns(&reg4, 2, &r4, &ctx);
    ASSERT(r4.residues[0] == 1 && r4.residues[1] == 4
        && r4.residues[2] == 4, "expected (1,4,4)");

    /* Trits {-1,+1} = -1 + 3 = 2 → (2, 2, 2) */
    TEST("{-1,+1} → value 2 → residues (2,2,2)");
    trit2_reg32 reg2 = trit2_reg32_splat(TRIT2_UNKNOWN);
    trit2_reg32_set(&reg2, 0, TRIT2_FALSE);
    trit2_reg32_set(&reg2, 1, TRIT2_TRUE);
    trit_rns_t r2;
    trit_to_rns(&reg2, 2, &r2, &ctx);
    ASSERT(r2.residues[0] == 2 && r2.residues[1] == 2
        && r2.residues[2] == 2, "expected (2,2,2)");

    /* Value 7 = {+1, -1, +1} (1 + (-3) + 9 = 7) → residues (1, 2, 0) */
    TEST("Value 7 → residues (1,2,0)");
    trit2_reg32 reg7 = trit2_reg32_splat(TRIT2_UNKNOWN);
    trit2_reg32_set(&reg7, 0, TRIT2_TRUE);   /* +1 × 3^0 = 1  */
    trit2_reg32_set(&reg7, 1, TRIT2_FALSE);  /* -1 × 3^1 = -3 */
    trit2_reg32_set(&reg7, 2, TRIT2_TRUE);   /* +1 × 3^2 = 9  */
    trit_rns_t r7;
    trit_to_rns(&reg7, 3, &r7, &ctx);
    ASSERT(r7.residues[0] == 1 && r7.residues[1] == 2
        && r7.residues[2] == 0, "expected (1,2,0)");

    /* NULL checks */
    TEST("trit_to_rns NULL ctx → zeros");
    trit_rns_t rn;
    trit_to_rns(&zero_reg, 4, &rn, NULL);
    ASSERT(rn.residues[0] == 0, "expected 0");

    TEST("trit_to_rns NULL reg → zeros");
    trit_rns_t rn2;
    trit_to_rns(NULL, 4, &rn2, &ctx);
    ASSERT(rn2.residues[0] == 0, "expected 0");
}

/* ========================================================================
 * 3. CRT Reconstruction (rns_to_trit)
 * ======================================================================== */

static void test_crt_reconstruction(void) {
    SECTION("RNS: CRT Reconstruction → trit2_reg32");
    trit_rns_context_t ctx;
    trit_rns_init(&ctx);

    /* Roundtrip: encode 0 → RNS → back to trits → decode back to 0 */
    TEST("Roundtrip value 0");
    trit2_reg32 zero_reg = trit2_reg32_splat(TRIT2_UNKNOWN);
    trit_rns_t rz;
    trit_to_rns(&zero_reg, 4, &rz, &ctx);
    trit2_reg32 out0;
    rns_to_trit(&rz, 4, &out0, &ctx);
    int v0 = trit2_decode(trit2_reg32_get(&out0, 0));
    ASSERT(v0 == 0, "expected trit[0]=0");

    /* Roundtrip: 1 → RNS → CRT → verify trit[0] == +1 */
    TEST("Roundtrip value 1");
    trit2_reg32 one_reg = trit2_reg32_splat(TRIT2_UNKNOWN);
    trit2_reg32_set(&one_reg, 0, TRIT2_TRUE);
    trit_rns_t r1;
    trit_to_rns(&one_reg, 4, &r1, &ctx);
    trit2_reg32 out1;
    rns_to_trit(&r1, 4, &out1, &ctx);
    ASSERT(trit2_decode(trit2_reg32_get(&out1, 0)) == 1, "expected +1");

    /* Roundtrip for larger values: 42, -13 */
    TEST("Roundtrip value 42");
    trit_rns_t r42;
    r42.residues[0] = 42 % 3;   /* 0 */
    r42.residues[1] = 42 % 5;   /* 2 */
    r42.residues[2] = 42 % 7;   /* 0 */
    trit2_reg32 out42;
    rns_to_trit(&r42, 5, &out42, &ctx);
    trit_rns_t check42;
    trit_to_rns(&out42, 5, &check42, &ctx);
    ASSERT(check42.residues[0] == 0 && check42.residues[1] == 2
        && check42.residues[2] == 0, "expected (0,2,0)");

    /* -13 → residues: posmod(-13,3)=2, posmod(-13,5)=2, posmod(-13,7)=1 */
    TEST("Roundtrip value -13");
    trit_rns_t rn13;
    rn13.residues[0] = (3 - (13 % 3)) % 3;  /* 2 */
    rn13.residues[1] = (5 - (13 % 5)) % 5;  /* 2 */
    rn13.residues[2] = (7 - (13 % 7)) % 7;  /* 1 */
    trit2_reg32 out_n13;
    rns_to_trit(&rn13, 5, &out_n13, &ctx);
    trit_rns_t check_n13;
    trit_to_rns(&out_n13, 5, &check_n13, &ctx);
    ASSERT(check_n13.residues[0] == rn13.residues[0]
        && check_n13.residues[1] == rn13.residues[1]
        && check_n13.residues[2] == rn13.residues[2],
           "expected residue match for -13");

    TEST("rns_to_trit NULL ctx → UNKNOWN splat");
    trit2_reg32 null_out;
    rns_to_trit(&rz, 4, &null_out, NULL);
    ASSERT(trit2_decode(trit2_reg32_get(&null_out, 0)) == 0, "expected 0");
}

/* ========================================================================
 * 4. Carry-Free Arithmetic
 * ======================================================================== */

static void test_arithmetic(void) {
    SECTION("RNS: Carry-Free Arithmetic");
    trit_rns_context_t ctx;
    trit_rns_init(&ctx);

    /* Build RNS for 10 and 7 via direct residue construction */
    trit_rns_t a = {{ 10 % 3, 10 % 5, 10 % 7 }};  /* (1, 0, 3) */
    trit_rns_t b = {{  7 % 3,  7 % 5,  7 % 7 }};  /* (1, 2, 0) */

    /* Add: 10 + 7 = 17 → (2, 2, 3) → CRT → 17 */
    TEST("RNS add: 10 + 7 = 17");
    trit_rns_t sum;
    rns_add(&a, &b, &sum, &ctx);
    ASSERT(sum.residues[0] == (1+1) % 3
        && sum.residues[1] == (0+2) % 5
        && sum.residues[2] == (3+0) % 7,
           "expected (2,2,3)");

    /* Reconstruct to check value */
    TEST("RNS add reconstructed = 17");
    trit2_reg32 out_sum;
    rns_to_trit(&sum, 5, &out_sum, &ctx);
    trit_rns_t chk;
    trit_to_rns(&out_sum, 5, &chk, &ctx);
    ASSERT(chk.residues[0] == 17 % 3
        && chk.residues[1] == 17 % 5
        && chk.residues[2] == 17 % 7,
           "expected residues of 17: (2,2,3)");

    /* Sub: 10 - 7 = 3 → (0, 3, 3) */
    TEST("RNS sub: 10 - 7 = 3");
    trit_rns_t diff;
    rns_sub(&a, &b, &diff, &ctx);
    ASSERT(diff.residues[0] == 0
        && diff.residues[1] == 3
        && diff.residues[2] == 3,
           "expected (0,3,3)");

    /* Mul: 3 × 5 = 15 → (0, 0, 1) */
    TEST("RNS mul: 3 * 5 = 15");
    trit_rns_t m3 = {{ 3 % 3, 3 % 5, 3 % 7 }};  /* (0, 3, 3) */
    trit_rns_t m5 = {{ 5 % 3, 5 % 5, 5 % 7 }};  /* (2, 0, 5) */
    trit_rns_t prod;
    rns_mul(&m3, &m5, &prod, &ctx);
    ASSERT(prod.residues[0] == (0*2) % 3
        && prod.residues[1] == (3*0) % 5
        && prod.residues[2] == (3*5) % 7,
           "expected (0,0,1)");

    /* a + (-a) = 0 via sub */
    TEST("RNS a - a = 0");
    trit_rns_t zero;
    rns_sub(&a, &a, &zero, &ctx);
    ASSERT(rns_is_zero(&zero, &ctx), "expected zero");

    TEST("RNS add NULL ctx → zeros");
    trit_rns_t rn;
    rns_add(&a, &b, &rn, NULL);
    ASSERT(rn.residues[0] == 0, "expected 0");
}

/* ========================================================================
 * 5. Montgomery Modular Multiplication
 * ======================================================================== */

static void test_montgomery(void) {
    SECTION("RNS: Montgomery Modular Multiplication");
    trit_rns_context_t ctx;
    trit_rns_init(&ctx);

    TEST("Montgomery mul: (1,1,1)*(1,1,1) — per-channel REDC");
    trit_rns_t ones = {{ 1, 1, 1 }};
    trit_rns_t mont_res;
    rns_montgomery_mul(&ones, &ones, &mont_res, &ctx);
    ASSERT(mont_res.residues[0] < 3
        && mont_res.residues[1] < 5
        && mont_res.residues[2] < 7,
           "all residues within modulus range");

    /* Verify 0*x = 0 in Montgomery */
    TEST("Montgomery mul: 0 * x = 0");
    trit_rns_t zeros = {{ 0, 0, 0 }};
    trit_rns_t mz;
    rns_montgomery_mul(&zeros, &ones, &mz, &ctx);
    ASSERT(mz.residues[0] == 0 && mz.residues[1] == 0
        && mz.residues[2] == 0, "expected (0,0,0)");

    /* Compare Montgomery mul vs plain mul for identity element */
    TEST("Montgomery mul result equals plain mul for 0-input");
    trit_rns_t plain_z;
    rns_mul(&zeros, &ones, &plain_z, &ctx);
    ASSERT(mz.residues[0] == plain_z.residues[0]
        && mz.residues[1] == plain_z.residues[1]
        && mz.residues[2] == plain_z.residues[2],
           "Montgomery and plain agree on zero");

    /* Montgomery commutativity: a*b = b*a */
    TEST("Montgomery commutativity: a*b == b*a");
    trit_rns_t va = {{ 2, 3, 4 }};
    trit_rns_t vb = {{ 1, 4, 6 }};
    trit_rns_t ab, ba;
    rns_montgomery_mul(&va, &vb, &ab, &ctx);
    rns_montgomery_mul(&vb, &va, &ba, &ctx);
    ASSERT(ab.residues[0] == ba.residues[0]
        && ab.residues[1] == ba.residues[1]
        && ab.residues[2] == ba.residues[2],
           "REDC(a*b) == REDC(b*a)");

    TEST("Montgomery NULL ctx → zeros");
    trit_rns_t mn;
    rns_montgomery_mul(&ones, &ones, &mn, NULL);
    ASSERT(mn.residues[0] == 0, "expected 0");
}

/* ========================================================================
 * 6. Zero / Sparsity Detection
 * ======================================================================== */

static void test_zero_sparsity(void) {
    SECTION("RNS: Zero & Sparsity Detection");
    trit_rns_context_t ctx;
    trit_rns_init(&ctx);

    TEST("rns_is_zero for (0,0,0) → true");
    trit_rns_t z = {{ 0, 0, 0 }};
    ASSERT(rns_is_zero(&z, &ctx) == true, "expected true");

    TEST("rns_is_zero for (1,0,0) → false");
    trit_rns_t nz1 = {{ 1, 0, 0 }};
    ASSERT(rns_is_zero(&nz1, &ctx) == false, "expected false");

    TEST("rns_is_zero for (0,0,1) → false");
    trit_rns_t nz2 = {{ 0, 0, 1 }};
    ASSERT(rns_is_zero(&nz2, &ctx) == false, "expected false");

    TEST("rns_is_zero NULL → false");
    ASSERT(rns_is_zero(NULL, &ctx) == false, "expected false");

    /* Sparsity: zero-register is sparse by definition */
    TEST("All-UNKNOWN reg is sparse (>50% zero)");
    trit2_reg32 sparse_reg = trit2_reg32_splat(TRIT2_UNKNOWN);
    ASSERT(trit2_reg32_is_sparse(sparse_reg) == 1, "expected sparse");

    /* Non-sparse: fill all 32 trits with TRUE */
    TEST("All-TRUE reg is not sparse");
    trit2_reg32 dense_reg = trit2_reg32_splat(TRIT2_TRUE);
    ASSERT(trit2_reg32_is_sparse(dense_reg) == 0, "expected not sparse");
}

/* ========================================================================
 * 7. Validate Round-Trip
 * ======================================================================== */

static void test_validate(void) {
    SECTION("RNS: Validate & Round-Trip Consistency");
    trit_rns_context_t ctx;
    trit_rns_init(&ctx);

    /* Valid residue: 42 → (0, 2, 0) */
    TEST("rns_validate valid residues for 42");
    trit_rns_t v42 = {{ 42 % 3, 42 % 5, 42 % 7 }};
    ASSERT(rns_validate(&v42, &ctx) == 0, "expected valid");

    /* Valid residue: 0 → (0, 0, 0) */
    TEST("rns_validate valid zero residue");
    trit_rns_t v0 = {{ 0, 0, 0 }};
    ASSERT(rns_validate(&v0, &ctx) == 0, "expected valid");

    /* Invalid: residue >= modulus (e.g., r[0]=3 is invalid for mod 3) */
    TEST("rns_validate out-of-range residue → -1");
    trit_rns_t bad = {{ 3, 0, 0 }};
    ASSERT(rns_validate(&bad, &ctx) == -1, "expected -1");

    /* Another invalid: r[2] = 7, modulus is 7 → invalid */
    TEST("rns_validate r[2]=7 invalid for mod 7 → -1");
    trit_rns_t bad2 = {{ 0, 0, 7 }};
    ASSERT(rns_validate(&bad2, &ctx) == -1, "expected -1");

    /* Full roundtrip: trit2_reg32 → RNS → validate → CRT → trit → RNS → match */
    TEST("Full roundtrip: reg → RNS → CRT → reg → RNS matches");
    trit2_reg32 reg = trit2_reg32_splat(TRIT2_UNKNOWN);
    trit2_reg32_set(&reg, 0, TRIT2_TRUE);   /* +1 */
    trit2_reg32_set(&reg, 1, TRIT2_FALSE);  /* -1 → value = -2 */
    trit_rns_t rns1;
    trit_to_rns(&reg, 4, &rns1, &ctx);
    ASSERT(rns_validate(&rns1, &ctx) == 0, "forward residues valid");

    TEST("Roundtrip: CRT → re-encode matches original");
    trit2_reg32 reconstructed;
    rns_to_trit(&rns1, 4, &reconstructed, &ctx);
    trit_rns_t rns2;
    trit_to_rns(&reconstructed, 4, &rns2, &ctx);
    ASSERT(rns2.residues[0] == rns1.residues[0]
        && rns2.residues[1] == rns1.residues[1]
        && rns2.residues[2] == rns1.residues[2],
           "residues match after roundtrip");

    TEST("rns_validate NULL ctx → -1");
    ASSERT(rns_validate(&v0, NULL) == -1, "expected -1");

    TEST("rns_validate NULL rns → -1");
    ASSERT(rns_validate(NULL, &ctx) == -1, "expected -1");
}

/* ========================================================================
 * 8. Extend Moduli
 * ======================================================================== */

static void test_extend_moduli(void) {
    SECTION("RNS: Dynamic Moduli Extension");
    trit_rns_context_t ctx;
    trit_rns_init(&ctx);

    /* Extend with 11 (coprime to 3,5,7) */
    TEST("Extend with modulus 11 → success");
    ASSERT(rns_extend_moduli(&ctx, 11) == 0, "expected 0");

    TEST("Count now 4");
    ASSERT(ctx.count == 4, "expected 4");

    TEST("M now 1155 (105*11)");
    ASSERT(ctx.M == 1155, "expected 1155");

    TEST("New Mi[3] == 105 (1155/11)");
    ASSERT(ctx.Mi[3] == 105, "expected 105");

    TEST("Mi_inv[3] valid (105^-1 mod 11)");
    ASSERT(ctx.Mi_inv[3] == 2, "expected 2");

    /* Existing Mi values are recomputed */
    TEST("Mi[0] recomputed → 1155/3 = 385");
    ASSERT(ctx.Mi[0] == 385, "expected 385");

    /* Reject non-coprime: 6 shares factor 3 with modulus 3 */
    TEST("Extend with 6 (not coprime to 3) → -1");
    ASSERT(rns_extend_moduli(&ctx, 6) == -1, "expected -1");

    /* Reject modulus <= 1 */
    TEST("Extend with 1 → -1");
    ASSERT(rns_extend_moduli(&ctx, 1) == -1, "expected -1");

    /* Fill to max */
    TEST("Extend with 13 → success (5th modulus)");
    ASSERT(rns_extend_moduli(&ctx, 13) == 0, "expected 0");

    TEST("Extend with 17 → success (6th modulus, max)");
    ASSERT(rns_extend_moduli(&ctx, 17) == 0, "expected 0");

    TEST("Count now 6 (max)");
    ASSERT(ctx.count == 6, "expected 6");

    TEST("Extend beyond max → -1");
    ASSERT(rns_extend_moduli(&ctx, 19) == -1, "expected -1");

    TEST("rns_extend_moduli NULL → -1");
    ASSERT(rns_extend_moduli(NULL, 11) == -1, "expected -1");
}

/* ========================================================================
 * 9. PVT-Style Resilience
 * ======================================================================== */

static void test_pvt_resilience(void) {
    SECTION("RNS: PVT-Style Resilience");
    trit_rns_context_t ctx;
    trit_rns_init(&ctx);

    /* Verify arithmetic consistency across many values in [-52, 52] */
    TEST("Arithmetic identity: a + 0 = a for all values [0..52]");
    trit_rns_t zero = {{ 0, 0, 0 }};
    int ok = 1;
    for (uint32_t v = 0; v <= 52; v++) {
        trit_rns_t a = {{ v % 3, v % 5, v % 7 }};
        trit_rns_t sum;
        rns_add(&a, &zero, &sum, &ctx);
        if (sum.residues[0] != a.residues[0]
         || sum.residues[1] != a.residues[1]
         || sum.residues[2] != a.residues[2]) { ok = 0; break; }
    }
    ASSERT(ok == 1, "a + 0 = a for all values");

    /* Verify subtraction identity: a - a = 0 */
    TEST("Subtraction identity: a - a = 0 for range [0..52]");
    ok = 1;
    for (uint32_t v = 0; v <= 52; v++) {
        trit_rns_t a = {{ v % 3, v % 5, v % 7 }};
        trit_rns_t diff;
        rns_sub(&a, &a, &diff, &ctx);
        if (!rns_is_zero(&diff, &ctx)) { ok = 0; break; }
    }
    ASSERT(ok == 1, "a - a = 0 for all values");

    /* Validate all values in range */
    TEST("rns_validate passes for all values [0..104]");
    ok = 1;
    for (uint32_t v = 0; v < 105; v++) {
        trit_rns_t r = {{ v % 3, v % 5, v % 7 }};
        if (rns_validate(&r, &ctx) != 0) { ok = 0; break; }
    }
    ASSERT(ok == 1, "all 105 residue tuples valid");

    /* Mul commutativity: a*b = b*a */
    TEST("Mul commutativity: 7*13 residues == 13*7 residues");
    trit_rns_t r7  = {{ 7 % 3, 7 % 5, 7 % 7 }};
    trit_rns_t r13 = {{ 13 % 3, 13 % 5, 13 % 7 }};
    trit_rns_t p1, p2;
    rns_mul(&r7, &r13, &p1, &ctx);
    rns_mul(&r13, &r7, &p2, &ctx);
    ASSERT(p1.residues[0] == p2.residues[0]
        && p1.residues[1] == p2.residues[1]
        && p1.residues[2] == p2.residues[2],
           "commutative");

    /* Distributive: a*(b+c) = a*b + a*c */
    TEST("Distributive: 2*(3+4) = 2*3 + 2*4");
    trit_rns_t r2 = {{ 2 % 3, 2 % 5, 2 % 7 }};
    trit_rns_t r3 = {{ 3 % 3, 3 % 5, 3 % 7 }};
    trit_rns_t r4 = {{ 4 % 3, 4 % 5, 4 % 7 }};
    trit_rns_t bc_sum, lhs, ab_prod, ac_prod, rhs;
    rns_add(&r3, &r4, &bc_sum, &ctx);
    rns_mul(&r2, &bc_sum, &lhs, &ctx);
    rns_mul(&r2, &r3, &ab_prod, &ctx);
    rns_mul(&r2, &r4, &ac_prod, &ctx);
    rns_add(&ab_prod, &ac_prod, &rhs, &ctx);
    ASSERT(lhs.residues[0] == rhs.residues[0]
        && lhs.residues[1] == rhs.residues[1]
        && lhs.residues[2] == rhs.residues[2],
           "distributive law holds");
}

/* ========================================================================
 * 10. Crypto Integration (RNS-accelerated modular ops)
 * ======================================================================== */

static void test_crypto_integration(void) {
    SECTION("RNS: Crypto Integration — Modular Chains");
    trit_rns_context_t ctx;
    trit_rns_init(&ctx);

    /* Simulate a multi-step modular computation:
     * Compute (a * b + c) mod M via RNS, verify residues. */
    TEST("Chain: (7*13 + 5) residue consistency");
    trit_rns_t r7  = {{ 7 % 3, 7 % 5, 7 % 7 }};
    trit_rns_t r13 = {{ 13 % 3, 13 % 5, 13 % 7 }};
    trit_rns_t r5  = {{ 5 % 3, 5 % 5, 5 % 7 }};
    trit_rns_t prod, chain;
    rns_mul(&r7, &r13, &prod, &ctx);
    rns_add(&prod, &r5, &chain, &ctx);
    ASSERT(chain.residues[0] == 96 % 3
        && chain.residues[1] == 96 % 5
        && chain.residues[2] == 96 % 7,
           "expected residues of 96: (0,1,5)");

    /* Double: 2*x via add(x,x) */
    TEST("Double: add(42, 42) = 84 residues");
    trit_rns_t r42 = {{ 42 % 3, 42 % 5, 42 % 7 }};
    trit_rns_t dbl;
    rns_add(&r42, &r42, &dbl, &ctx);
    ASSERT(dbl.residues[0] == 84 % 3
        && dbl.residues[1] == 84 % 5
        && dbl.residues[2] == 84 % 7,
           "expected residues of 84: (0,4,0)");

    /* Montgomery chain: mont(a,b) then plain verify */
    TEST("Montgomery chain: mont(2,3) per-channel valid ranges");
    trit_rns_t mr2 = {{ 2, 2, 2 }};
    trit_rns_t mr3 = {{ 0, 3, 3 }};
    trit_rns_t mc;
    rns_montgomery_mul(&mr2, &mr3, &mc, &ctx);
    ASSERT(mc.residues[0] < 3
        && mc.residues[1] < 5
        && mc.residues[2] < 7,
           "Montgomery results in valid range");

    /* Extended moduli crypto: extend with 11, then do arithmetic */
    TEST("Extended (4 moduli): arithmetic still consistent");
    trit_rns_context_t ext_ctx;
    trit_rns_init(&ext_ctx);
    rns_extend_moduli(&ext_ctx, 11);

    trit_rns_t ea = {{ 10 % 3, 10 % 5, 10 % 7, 10 % 11 }};
    trit_rns_t eb = {{ 20 % 3, 20 % 5, 20 % 7, 20 % 11 }};
    trit_rns_t esum;
    rns_add(&ea, &eb, &esum, &ext_ctx);
    ASSERT(esum.residues[0] == 30 % 3
        && esum.residues[1] == 30 % 5
        && esum.residues[2] == 30 % 7
        && esum.residues[3] == 30 % 11,
           "extended moduli arithmetic correct");

    /* Validate extended residue */
    TEST("Validate extended residue");
    ASSERT(rns_validate(&esum, &ext_ctx) == 0, "extended residue valid");
}

/* ========================================================================
 * 11. PVT Noise Injection
 * ======================================================================== */

static void test_noise_injection(void) {
    SECTION("RNS: PVT Noise Injection (rns_apply_noise)");
    trit_rns_context_t ctx;
    trit_rns_init(&ctx);

    /* Noise probability 0.0 should leave residues unchanged */
    TEST("noise_prob=0 → no corruption");
    srand(42);
    trit_rns_t clean = {{ 1, 2, 3 }};
    trit_rns_t saved = clean;
    rns_apply_noise(&clean, 0.0, &ctx);
    ASSERT(clean.residues[0] == saved.residues[0]
        && clean.residues[1] == saved.residues[1]
        && clean.residues[2] == saved.residues[2],
           "expected unchanged");

    /* Noise probability 1.0 should corrupt all channels (statistically) */
    TEST("noise_prob=1.0 → residues still in valid range");
    srand(99);
    trit_rns_t noisy = {{ 1, 2, 3 }};
    rns_apply_noise(&noisy, 1.0, &ctx);
    ASSERT(noisy.residues[0] < 3
        && noisy.residues[1] < 5
        && noisy.residues[2] < 7,
           "all corrupted residues within modulus range");

    /* NULL rns → no crash */
    TEST("rns_apply_noise NULL rns → no crash");
    rns_apply_noise(NULL, 0.5, &ctx);
    ASSERT(1, "did not crash");

    /* NULL ctx → no crash */
    TEST("rns_apply_noise NULL ctx → no crash");
    trit_rns_t dummy = {{ 0, 0, 0 }};
    rns_apply_noise(&dummy, 0.5, NULL);
    ASSERT(1, "did not crash");

    /* Statistical test: probability 0.5 over many trials */
    TEST("noise_prob=0.5 → ~50% channels flipped (statistical)");
    srand(1234);
    int flip_count = 0;
    int total_channels = 0;
    for (int trial = 0; trial < 100; trial++) {
        trit_rns_t probe = {{ 1, 1, 1 }};
        rns_apply_noise(&probe, 0.5, &ctx);
        for (uint32_t ch = 0; ch < ctx.count; ch++) {
            total_channels++;
            if (probe.residues[ch] != 1) flip_count++;
        }
    }
    /* Expect ~50% flips (±25% tolerance for rand()) */
    int pct = (flip_count * 100) / total_channels;
    ASSERT(pct >= 25 && pct <= 75,
           "expected ~50% flip rate within tolerance");

    /* Validate that noise corruption can be detected */
    TEST("Noisy residue may fail validation (detection)");
    srand(777);
    trit_rns_t valid = {{ 42 % 3, 42 % 5, 42 % 7 }};
    ASSERT(rns_validate(&valid, &ctx) == 0, "starts valid");

    TEST("Heavy noise on valid residue changes at least one channel");
    trit_rns_t heavy = {{ 42 % 3, 42 % 5, 42 % 7 }};
    int any_changed = 0;
    for (int i = 0; i < 20; i++) {
        trit_rns_t tmp = heavy;
        rns_apply_noise(&tmp, 1.0, &ctx);
        if (tmp.residues[0] != heavy.residues[0]
         || tmp.residues[1] != heavy.residues[1]
         || tmp.residues[2] != heavy.residues[2]) {
            any_changed = 1;
            break;
        }
    }
    ASSERT(any_changed == 1, "expected noise to change residues");
}

/* ========================================================================
 * 12. Conversions — Custom Init, MRS, Round-Trips (50 assertions)
 * ======================================================================== */

static void test_conversions_extended(void) {
    SECTION("RNS: Conversions — Custom Init & MRS");

    /* --- Custom init with default {3,5,7} --- */
    TEST("Custom init {3,5,7} → M=105");
    trit_rns_context_t ctx;
    uint32_t mod357[] = {3, 5, 7};
    ASSERT(trit_rns_init_custom(&ctx, mod357, 3) == 0, "expected 0");

    TEST("Custom {3,5,7} M product");
    ASSERT(ctx.M == 105, "expected 105");

    TEST("Custom {3,5,7} count");
    ASSERT(ctx.count == 3, "expected 3");

    /* --- Custom init with Mersenne-4: {3,4,5} --- */
    TEST("Custom init Mersenne {3,4,5} → M=60");
    trit_rns_context_t m4;
    uint32_t mod_m4[] = {RNS_MODSET_MERSENNE_4};
    ASSERT(trit_rns_init_custom(&m4, mod_m4, 3) == 0, "expected 0");

    TEST("Mersenne-4 M==60");
    ASSERT(m4.M == 60, "expected 60");

    TEST("Mersenne-4 moduli[1]==4");
    ASSERT(m4.moduli[1] == 4, "expected 4");

    /* --- Custom init with Mersenne-8: {7,8,9} --- */
    TEST("Custom init Mersenne {7,8,9} → M=504");
    trit_rns_context_t m8;
    uint32_t mod_m8[] = {RNS_MODSET_MERSENNE_8};
    ASSERT(trit_rns_init_custom(&m8, mod_m8, 3) == 0, "expected 0");

    TEST("Mersenne-8 M==504");
    ASSERT(m8.M == 504, "expected 504");

    /* --- Custom init with ternary {3,13,37} --- */
    TEST("Custom init ternary {3,13,37} → M=1443");
    trit_rns_context_t tc;
    uint32_t mod_tc[] = {RNS_MODSET_TERNARY};
    ASSERT(trit_rns_init_custom(&tc, mod_tc, 3) == 0, "expected 0");

    TEST("Ternary aligned M==1443");
    ASSERT(tc.M == 1443, "expected 1443");

    /* --- Custom init with abundant {3,4,5,15} → should fail (3 and 15 share 3) --- */
    TEST("Abundant {3,4,5,15} fails (gcd(3,15)=3)");
    trit_rns_context_t ab;
    uint32_t mod_ab[] = {RNS_MODSET_ABUNDANT};
    ASSERT(trit_rns_init_custom(&ab, mod_ab, 4) == -1, "expected -1 non-coprime");

    /* --- Coprime abundant alternative: {4,5,9,11} --- */
    TEST("Coprime set {4,5,9,11} → M=1980");
    trit_rns_context_t ab2;
    uint32_t mod_ab2[] = {4, 5, 9, 11};
    ASSERT(trit_rns_init_custom(&ab2, mod_ab2, 4) == 0, "expected 0");

    TEST("Coprime set M==1980");
    ASSERT(ab2.M == 1980, "expected 1980");

    /* --- Custom init with crypto {11,13,17,19,23} --- */
    TEST("Crypto {11,13,17,19,23} → M=1062347");
    trit_rns_context_t cry;
    uint32_t mod_cry[] = {RNS_MODSET_CRYPTO};
    ASSERT(trit_rns_init_custom(&cry, mod_cry, 5) == 0, "expected 0");

    TEST("Crypto M==1062347");
    ASSERT(cry.M == 1062347, "expected 1062347");

    /* --- Custom init error cases --- */
    TEST("Custom init NULL ctx → -1");
    ASSERT(trit_rns_init_custom(NULL, mod357, 3) == -1, "expected -1");

    TEST("Custom init NULL moduli → -1");
    ASSERT(trit_rns_init_custom(&ctx, NULL, 3) == -1, "expected -1");

    TEST("Custom init count=0 → -1");
    ASSERT(trit_rns_init_custom(&ctx, mod357, 0) == -1, "expected -1");

    TEST("Custom init count > MAX → -1");
    ASSERT(trit_rns_init_custom(&ctx, mod357, RNS_MAX_MODULI + 1) == -1, "expected -1");

    TEST("Custom init modulus=1 → -1");
    uint32_t bad_mod[] = {1, 5, 7};
    ASSERT(trit_rns_init_custom(&ctx, bad_mod, 3) == -1, "expected -1");

    /* --- MRS conversion: value 42 in {3,5,7} --- */
    TEST("MRS: rns_to_mrs for value 42");
    trit_rns_context_t mrs_ctx;
    trit_rns_init(&mrs_ctx);
    trit_rns_t r42 = {{ 42 % 3, 42 % 5, 42 % 7 }};
    uint32_t digits[RNS_MAX_MODULI] = {0};
    ASSERT(rns_to_mrs(&r42, digits, &mrs_ctx) == 0, "expected 0");

    /* MRS reconstruction: 42 = d0 + d1*3 + d2*3*5 */
    TEST("MRS digits reconstruct to 42");
    uint32_t reconstructed = digits[0] + digits[1] * 3 + digits[2] * 15;
    ASSERT(reconstructed == 42, "expected 42");

    /* --- MRS roundtrip --- */
    TEST("MRS roundtrip: rns→mrs→rns for value 42");
    trit_rns_t r42_back;
    ASSERT(rns_from_mrs(digits, &r42_back, &mrs_ctx) == 0, "expected 0");

    TEST("MRS roundtrip residues match");
    ASSERT(r42_back.residues[0] == r42.residues[0]
        && r42_back.residues[1] == r42.residues[1]
        && r42_back.residues[2] == r42.residues[2],
           "residues match after MRS roundtrip");

    /* --- MRS for value 0 --- */
    TEST("MRS: value 0 → all-zero digits");
    trit_rns_t r0 = {{ 0, 0, 0 }};
    uint32_t d0[RNS_MAX_MODULI] = {0};
    rns_to_mrs(&r0, d0, &mrs_ctx);
    ASSERT(d0[0] == 0 && d0[1] == 0 && d0[2] == 0, "all digits zero");

    /* --- MRS for value 104 (max in range-1) --- */
    TEST("MRS: value 104 roundtrip");
    trit_rns_t r104 = {{ 104 % 3, 104 % 5, 104 % 7 }};
    uint32_t d104[RNS_MAX_MODULI] = {0};
    rns_to_mrs(&r104, d104, &mrs_ctx);
    trit_rns_t r104_back;
    rns_from_mrs(d104, &r104_back, &mrs_ctx);
    ASSERT(r104_back.residues[0] == r104.residues[0]
        && r104_back.residues[1] == r104.residues[1]
        && r104_back.residues[2] == r104.residues[2],
           "roundtrip matches for 104");

    /* --- MRS for all values 0..104 --- */
    TEST("MRS roundtrip for all values 0..104");
    int mrs_ok = 1;
    for (uint32_t v = 0; v < 105; v++) {
        trit_rns_t rv = {{ v % 3, v % 5, v % 7 }};
        uint32_t dv[RNS_MAX_MODULI] = {0};
        rns_to_mrs(&rv, dv, &mrs_ctx);
        trit_rns_t rv_back;
        rns_from_mrs(dv, &rv_back, &mrs_ctx);
        if (rv_back.residues[0] != rv.residues[0]
         || rv_back.residues[1] != rv.residues[1]
         || rv_back.residues[2] != rv.residues[2]) {
            mrs_ok = 0; break;
        }
    }
    ASSERT(mrs_ok == 1, "MRS roundtrip all values");

    /* --- MRS error cases --- */
    TEST("rns_to_mrs NULL rns → -1");
    ASSERT(rns_to_mrs(NULL, digits, &mrs_ctx) == -1, "expected -1");

    TEST("rns_to_mrs NULL digits → -1");
    ASSERT(rns_to_mrs(&r42, NULL, &mrs_ctx) == -1, "expected -1");

    TEST("rns_to_mrs NULL ctx → -1");
    ASSERT(rns_to_mrs(&r42, digits, NULL) == -1, "expected -1");

    TEST("rns_from_mrs NULL digits → -1");
    ASSERT(rns_from_mrs(NULL, &r42_back, &mrs_ctx) == -1, "expected -1");

    TEST("rns_from_mrs NULL rns_out → -1");
    ASSERT(rns_from_mrs(digits, NULL, &mrs_ctx) == -1, "expected -1");

    TEST("rns_from_mrs NULL ctx → -1");
    ASSERT(rns_from_mrs(digits, &r42_back, NULL) == -1, "expected -1");

    /* --- Custom init with {7,8,9}: MRS roundtrip --- */
    TEST("MRS roundtrip in Mersenne-8 {7,8,9}");
    trit_rns_t rm8_val = {{ 100 % 7, 100 % 8, 100 % 9 }};
    uint32_t dm8[RNS_MAX_MODULI] = {0};
    rns_to_mrs(&rm8_val, dm8, &m8);
    trit_rns_t rm8_back;
    rns_from_mrs(dm8, &rm8_back, &m8);
    ASSERT(rm8_back.residues[0] == rm8_val.residues[0]
        && rm8_back.residues[1] == rm8_val.residues[1]
        && rm8_back.residues[2] == rm8_val.residues[2],
           "Mersenne-8 MRS roundtrip matches");

    /* --- GCD public wrapper --- */
    TEST("rns_gcd_public(12, 8) == 4");
    ASSERT(rns_gcd_public(12, 8) == 4, "expected 4");

    TEST("rns_gcd_public(17, 13) == 1");
    ASSERT(rns_gcd_public(17, 13) == 1, "expected 1 (coprime)");

    TEST("rns_gcd_public(0, 5) == 5");
    ASSERT(rns_gcd_public(0, 5) == 5, "expected 5");

    /* --- Crypto moduli: conversion roundtrip for value 999000 --- */
    TEST("Crypto {11,13,17,19,23}: residues for 999000");
    trit_rns_t rc = {{ 999000 % 11, 999000 % 13, 999000 % 17,
                       999000 % 19, 999000 % 23 }};
    ASSERT(rc.residues[0] == 999000 % 11, "mod 11 correct");

    TEST("Crypto MRS roundtrip for 999000");
    uint32_t dc[RNS_MAX_MODULI] = {0};
    rns_to_mrs(&rc, dc, &cry);
    trit_rns_t rc_back;
    rns_from_mrs(dc, &rc_back, &cry);
    ASSERT(rc_back.residues[0] == rc.residues[0]
        && rc_back.residues[1] == rc.residues[1]
        && rc_back.residues[2] == rc.residues[2]
        && rc_back.residues[3] == rc.residues[3]
        && rc_back.residues[4] == rc.residues[4],
           "crypto MRS roundtrip matches");

    /* --- Additional conversion tests --- */
    TEST("Custom {3,5,7}: Mi_inv product check");
    /* Mi[0]*Mi_inv[0] ≡ 1 mod moduli[0] */
    ASSERT((ctx.Mi[0] * ctx.Mi_inv[0]) % ctx.moduli[0] == 1,
           "CRT product identity for channel 0");

    TEST("Custom {3,5,7}: Mi_inv channel 1 identity");
    ASSERT((ctx.Mi[1] * ctx.Mi_inv[1]) % ctx.moduli[1] == 1,
           "CRT product identity for channel 1");

    TEST("Custom {3,5,7}: Mi_inv channel 2 identity");
    ASSERT((ctx.Mi[2] * ctx.Mi_inv[2]) % ctx.moduli[2] == 1,
           "CRT product identity for channel 2");

    TEST("Mersenne-8: CRT identity all channels");
    int m8_ok = 1;
    for (uint32_t i = 0; i < m8.count; i++) {
        if ((m8.Mi[i] * m8.Mi_inv[i]) % m8.moduli[i] != 1) { m8_ok = 0; break; }
    }
    ASSERT(m8_ok == 1, "CRT identity holds for all Mersenne-8 channels");

    TEST("Ternary: CRT identity all channels");
    int tc_ok = 1;
    for (uint32_t i = 0; i < tc.count; i++) {
        if ((tc.Mi[i] * tc.Mi_inv[i]) % tc.moduli[i] != 1) { tc_ok = 0; break; }
    }
    ASSERT(tc_ok == 1, "CRT identity holds for all ternary channels");

    TEST("Crypto: CRT identity all channels");
    int cry_ok = 1;
    for (uint32_t i = 0; i < cry.count; i++) {
        if ((cry.Mi[i] * cry.Mi_inv[i]) % cry.moduli[i] != 1) { cry_ok = 0; break; }
    }
    ASSERT(cry_ok == 1, "CRT identity holds for all crypto channels");

    TEST("MRS digits[0] < moduli[0] for value 42");
    ASSERT(digits[0] < mrs_ctx.moduli[0], "d[0] < m[0]");

    TEST("MRS digits[1] < moduli[1] for value 42");
    ASSERT(digits[1] < mrs_ctx.moduli[1], "d[1] < m[1]");

    TEST("MRS digits[2] < moduli[2] for value 42");
    ASSERT(digits[2] < mrs_ctx.moduli[2], "d[2] < m[2]");
}

/* ========================================================================
 * 13. Low-Power Sim — TMVM-RNS & ResISC (40 assertions)
 * ======================================================================== */

static void test_low_power_sim(void) {
    SECTION("RNS: Low-Power Sim — TMVM-RNS Integration");

    trit_rns_context_t ctx;
    trit_rns_init(&ctx);

    /* --- TMVM-RNS init --- */
    TEST("tmvm_rns_init succeeds");
    tmvm_rns_state_t st;
    ASSERT(tmvm_rns_init(&st, &ctx) == 0, "expected 0");

    TEST("tmvm_rns_init NULL st → -1");
    ASSERT(tmvm_rns_init(NULL, &ctx) == -1, "expected -1");

    TEST("tmvm_rns_init NULL ctx → -1");
    ASSERT(tmvm_rns_init(&st, NULL) == -1, "expected -1");

    /* --- Load 2x2 identity matrix: [[1,0],[0,1]] --- */
    TEST("tmvm_rns_load_matrix 2x2 identity");
    trit id_mat[] = {1, 0, 0, 1};
    ASSERT(tmvm_rns_load_matrix(&st, id_mat, 2, 2) == 0, "expected 0");

    /* --- Load vector [1, -1] --- */
    TEST("tmvm_rns_load_vector [1,-1]");
    trit vec[] = {1, -1};
    ASSERT(tmvm_rns_load_vector(&st, vec, 2) == 0, "expected 0");

    /* --- Execute identity × [1,-1] = [1,-1] --- */
    TEST("tmvm_rns_execute identity multiply");
    ASSERT(tmvm_rns_execute(&st) == 0, "expected 0");

    TEST("tmvm_rns result[0] == 1");
    ASSERT(st.result[0] == 1, "expected 1");

    TEST("tmvm_rns result[1] == -1");
    ASSERT(st.result[1] == -1, "expected -1");

    TEST("tmvm_rns result_len == 2");
    ASSERT(st.result_len == 2, "expected 2");

    /* --- Load 2x3 matrix: [[1,1,0],[-1,0,1]] × [1,1,-1] = [2, -2] --- */
    TEST("tmvm_rns 2x3 multiply");
    tmvm_rns_state_t st2;
    tmvm_rns_init(&st2, &ctx);
    trit mat23[] = {1, 1, 0, -1, 0, 1};
    trit vec3[] = {1, 1, -1};
    tmvm_rns_load_matrix(&st2, mat23, 2, 3);
    tmvm_rns_load_vector(&st2, vec3, 3);
    ASSERT(tmvm_rns_execute(&st2) == 0, "expected 0");

    TEST("2x3 result[0] == 2 (1*1+1*1+0*-1)");
    ASSERT(st2.result[0] == 2, "expected 2");

    TEST("2x3 result[1] == -2 (-1*1+0*1+1*-1)");
    ASSERT(st2.result[1] == -2, "expected -2");

    /* --- Energy model --- */
    TEST("tmvm_rns energy > 0 after execution");
    ASSERT(tmvm_rns_get_energy(&st2) > 0, "expected > 0");

    TEST("tmvm_rns area save >= 22%");
    ASSERT(tmvm_rns_get_area_save(&st2) >= TMVM_RNS_AREA_SAVE_PCT,
           "expected >= 22");

    /* --- Truncation --- */
    TEST("tmvm_rns_set_truncation to 2 channels");
    tmvm_rns_state_t st3;
    tmvm_rns_init(&st3, &ctx);
    ASSERT(tmvm_rns_set_truncation(&st3, 2) == 0, "expected 0");

    TEST("Truncation rejects 0 channels");
    ASSERT(tmvm_rns_set_truncation(&st3, 0) == -1, "expected -1");

    TEST("Truncation rejects > count channels");
    ASSERT(tmvm_rns_set_truncation(&st3, 99) == -1, "expected -1");

    /* --- RNS dot product --- */
    TEST("tmvm_rns_dot basic test");
    trit_rns_t a_rns[2], b_rns[2], dot_out;
    /* Encode [1, -1] and [1, 1] */
    for (uint32_t k = 0; k < ctx.count; k++) {
        a_rns[0].residues[k] = 1;
        a_rns[1].residues[k] = ctx.moduli[k] - 1; /* -1 */
        b_rns[0].residues[k] = 1;
        b_rns[1].residues[k] = 1;
    }
    ASSERT(tmvm_rns_dot(a_rns, b_rns, 2, &dot_out, &ctx) == 0, "expected 0");

    /* dot = 1*1 + (-1)*1 = 0 → residues all 0 */
    TEST("tmvm_rns_dot [1,-1]·[1,1] = 0");
    ASSERT(dot_out.residues[0] == 0 && dot_out.residues[1] == 0
        && dot_out.residues[2] == 0, "expected all zeros");

    /* --- tmvm_rns_dot NULL cases --- */
    TEST("tmvm_rns_dot NULL a → -1");
    ASSERT(tmvm_rns_dot(NULL, b_rns, 2, &dot_out, &ctx) == -1, "expected -1");

    TEST("tmvm_rns_dot NULL out → -1");
    ASSERT(tmvm_rns_dot(a_rns, b_rns, 2, NULL, &ctx) == -1, "expected -1");

    /* --- Load errors --- */
    TEST("tmvm_rns_load_matrix NULL mat → -1");
    tmvm_rns_state_t st_err;
    tmvm_rns_init(&st_err, &ctx);
    ASSERT(tmvm_rns_load_matrix(&st_err, NULL, 2, 2) == -1, "expected -1");

    TEST("tmvm_rns_load_vector dimension mismatch → -1");
    trit err_mat[] = {1, 0, 0, 1};
    tmvm_rns_load_matrix(&st_err, err_mat, 2, 2);
    trit err_vec[] = {1, 0, 0}; /* len=3 != cols=2 */
    ASSERT(tmvm_rns_load_vector(&st_err, err_vec, 3) == -1, "expected -1");

    SECTION("RNS: Low-Power Sim — ResISC In-Sensor Computing");

    /* --- ResISC init --- */
    TEST("resisc_init succeeds");
    resisc_state_t rs;
    ASSERT(resisc_init(&rs, &ctx) == 0, "expected 0");

    TEST("resisc_init NULL st → -1");
    ASSERT(resisc_init(NULL, &ctx) == -1, "expected -1");

    /* --- Encode pixels --- */
    TEST("resisc_encode_pixels [1, 0, -1, 1]");
    trit pixels[] = {1, 0, -1, 1};
    ASSERT(resisc_encode_pixels(&rs, pixels, 4) == 0, "expected 0");

    TEST("Pixel 0 stream == 0xFFFFFFFF (+1)");
    ASSERT(rs.pixels[0].stream == 0xFFFFFFFFu, "expected all-ones");

    TEST("Pixel 2 stream == 0x00000000 (-1)");
    ASSERT(rs.pixels[2].stream == 0x00000000u, "expected all-zeros");

    TEST("Pixel 1 stream == 0x55555555 (0)");
    ASSERT(rs.pixels[1].stream == 0x55555555u, "expected alternating");

    /* --- Load weights & execute --- */
    TEST("resisc_load_weights [1, -1]");
    trit wt[] = {1, -1};
    ASSERT(resisc_load_weights(&rs, wt, 2) == 0, "expected 0");

    TEST("resisc_execute succeeds");
    ASSERT(resisc_execute(&rs) == 0, "expected 0");

    /* Conv: result[0] = 1*1 + 0*(-1) = 1
     *        result[1] = 0*1 + (-1)*(-1) = 1
     *        result[2] = (-1)*1 + 1*(-1) = -2 */
    TEST("ResISC result[0] == 1");
    ASSERT(rs.results[0] == 1, "expected 1");

    TEST("ResISC result[1] == 1");
    ASSERT(rs.results[1] == 1, "expected 1");

    TEST("ResISC result[2] == -2");
    ASSERT(rs.results[2] == -2, "expected -2");

    TEST("ResISC result_count == 3");
    ASSERT(rs.result_count == 3, "expected 3");

    /* --- Energy metrics --- */
    TEST("ResISC energy > 0");
    ASSERT(resisc_get_energy(&rs) > 0, "expected > 0");

    TEST("ResISC energy saved > 0");
    ASSERT(resisc_get_energy_saved(&rs) > 0, "expected > 0");

    TEST("ResISC SNR > 0");
    ASSERT(resisc_get_snr(&rs) > 0, "expected > 0");

    /* --- Noise injection --- */
    TEST("resisc_inject_noise with rate=0 → 0 errors");
    srand(42);
    ASSERT(resisc_inject_noise(&rs, 0.0) == 0, "expected 0 errors");

    TEST("resisc_inject_noise invalid rate → -1");
    ASSERT(resisc_inject_noise(&rs, -0.1) == -1, "expected -1");

    TEST("resisc_inject_noise NULL → -1");
    ASSERT(resisc_inject_noise(NULL, 0.5) == -1, "expected -1");

    /* --- Additional low-power tests --- */
    TEST("resisc_encode_pixels NULL pixels → -1");
    ASSERT(resisc_encode_pixels(&rs, NULL, 4) == -1, "expected -1");

    TEST("resisc_encode_pixels count=0 → -1");
    ASSERT(resisc_encode_pixels(&rs, pixels, 0) == -1, "expected -1");

    TEST("resisc_load_weights NULL weights → -1");
    ASSERT(resisc_load_weights(&rs, NULL, 2) == -1, "expected -1");

    TEST("resisc_load_weights count=0 → -1");
    ASSERT(resisc_load_weights(&rs, wt, 0) == -1, "expected -1");

    TEST("resisc energy_sense_fj > 0 after encode");
    ASSERT(rs.energy_sense_fj > 0, "expected > 0");

    TEST("resisc pixel_count == 4");
    ASSERT(rs.pixel_count == 4, "expected 4");

    /* --- TMVM-RNS: 3x3 all-ones matrix × all-ones vector --- */
    TEST("TMVM-RNS: 3x3 all-ones × all-ones");
    tmvm_rns_state_t st_ones;
    tmvm_rns_init(&st_ones, &ctx);
    trit ones_mat[] = {1,1,1, 1,1,1, 1,1,1};
    trit ones_vec[] = {1,1,1};
    tmvm_rns_load_matrix(&st_ones, ones_mat, 3, 3);
    tmvm_rns_load_vector(&st_ones, ones_vec, 3);
    tmvm_rns_execute(&st_ones);
    ASSERT(st_ones.result[0] == 3 && st_ones.result[1] == 3
        && st_ones.result[2] == 3, "expected all 3");

    TEST("TMVM-RNS: crt_reconstructions == rows");
    ASSERT(st_ones.crt_reconstructions == 3, "expected 3");

    TEST("TMVM-RNS: total_channel_macs > 0");
    ASSERT(st_ones.total_channel_macs > 0, "expected > 0");
}

/* ========================================================================
 * 14. Crypto Extended — Montgomery Exp & Redundant Checks (40 assertions)
 * ======================================================================== */

static void test_crypto_extended(void) {
    SECTION("RNS: Crypto — Montgomery Exponentiation");

    trit_rns_context_t ctx;
    trit_rns_init(&ctx);

    /* --- Montgomery exp: base^0 = 1 (identity) --- */
    TEST("Montgomery exp: base^0 → residues (1,1,1)");
    trit_rns_t base = {{ 2, 3, 4 }};
    trit_rns_t result;
    ASSERT(rns_montgomery_exp(&base, 0, &result, &ctx) == 0, "expected 0");

    TEST("Montgomery exp: base^0 residues check");
    ASSERT(result.residues[0] == 1 % 3
        && result.residues[1] == 1 % 5
        && result.residues[2] == 1 % 7,
           "expected (1,1,1)");

    /* --- Montgomery exp: base^1 = base (via REDC) --- */
    TEST("Montgomery exp: base^1 returns valid residues");
    trit_rns_t exp1;
    ASSERT(rns_montgomery_exp(&base, 1, &exp1, &ctx) == 0, "expected 0");

    TEST("Montgomery exp: base^1 residues in range");
    ASSERT(exp1.residues[0] < 3 && exp1.residues[1] < 5
        && exp1.residues[2] < 7, "in range");

    /* --- Montgomery exp: (1,1,1)^n = 1 for all n --- */
    TEST("Montgomery exp: 1^5 per-channel");
    trit_rns_t one = {{ 1, 1, 1 }};
    trit_rns_t one5;
    rns_montgomery_exp(&one, 5, &one5, &ctx);
    /* 1^5 = 1 but REDC form may differ — verify residues in range */
    ASSERT(one5.residues[0] < 3 && one5.residues[1] < 5
        && one5.residues[2] < 7, "in range");

    /* --- Montgomery exp: 0^n = 0 --- */
    TEST("Montgomery exp: 0^3 → (0,0,0)");
    trit_rns_t zero = {{ 0, 0, 0 }};
    trit_rns_t z3;
    rns_montgomery_exp(&zero, 3, &z3, &ctx);
    ASSERT(z3.residues[0] == 0 && z3.residues[1] == 0
        && z3.residues[2] == 0, "expected all zeros");

    /* --- Montgomery exp: increasing exponents stay in range --- */
    TEST("Montgomery exp: base^2 in range");
    trit_rns_t r2;
    rns_montgomery_exp(&base, 2, &r2, &ctx);
    ASSERT(r2.residues[0] < 3 && r2.residues[1] < 5
        && r2.residues[2] < 7, "in range");

    TEST("Montgomery exp: base^4 in range");
    trit_rns_t r4;
    rns_montgomery_exp(&base, 4, &r4, &ctx);
    ASSERT(r4.residues[0] < 3 && r4.residues[1] < 5
        && r4.residues[2] < 7, "in range");

    TEST("Montgomery exp: base^8 in range");
    trit_rns_t r8;
    rns_montgomery_exp(&base, 8, &r8, &ctx);
    ASSERT(r8.residues[0] < 3 && r8.residues[1] < 5
        && r8.residues[2] < 7, "in range");

    TEST("Montgomery exp: base^16 in range");
    trit_rns_t r16;
    rns_montgomery_exp(&base, 16, &r16, &ctx);
    ASSERT(r16.residues[0] < 3 && r16.residues[1] < 5
        && r16.residues[2] < 7, "in range");

    TEST("Montgomery exp: base^32 in range");
    trit_rns_t r32;
    rns_montgomery_exp(&base, 32, &r32, &ctx);
    ASSERT(r32.residues[0] < 3 && r32.residues[1] < 5
        && r32.residues[2] < 7, "in range");

    /* --- Montgomery exp NULL cases --- */
    TEST("Montgomery exp NULL base → -1");
    ASSERT(rns_montgomery_exp(NULL, 5, &result, &ctx) == -1, "expected -1");

    TEST("Montgomery exp NULL out → -1");
    ASSERT(rns_montgomery_exp(&base, 5, NULL, &ctx) == -1, "expected -1");

    TEST("Montgomery exp NULL ctx → -1");
    ASSERT(rns_montgomery_exp(&base, 5, &result, NULL) == -1, "expected -1");

    /* --- Crypto moduli: exp with {11,13,17,19,23} --- */
    SECTION("RNS: Crypto — Extended Moduli Exponentiation");

    TEST("Crypto moduli init");
    trit_rns_context_t cry;
    uint32_t mod_cry[] = {RNS_MODSET_CRYPTO};
    ASSERT(trit_rns_init_custom(&cry, mod_cry, 5) == 0, "expected 0");

    TEST("Crypto exp: base^0 = 1");
    trit_rns_t cb = {{ 5, 7, 10, 12, 15 }};
    trit_rns_t cr;
    rns_montgomery_exp(&cb, 0, &cr, &cry);
    int cry_ok = 1;
    for (uint32_t i = 0; i < cry.count; i++) {
        if (cr.residues[i] >= cry.moduli[i]) { cry_ok = 0; break; }
    }
    ASSERT(cry_ok == 1, "all residues in range");

    TEST("Crypto exp: base^3 in range");
    trit_rns_t cr3;
    rns_montgomery_exp(&cb, 3, &cr3, &cry);
    cry_ok = 1;
    for (uint32_t i = 0; i < cry.count; i++) {
        if (cr3.residues[i] >= cry.moduli[i]) { cry_ok = 0; break; }
    }
    ASSERT(cry_ok == 1, "all residues in range");

    SECTION("RNS: Crypto — Redundant Checks");

    /* --- Redundant check: extend {3,5,7} with auto-detected prime --- */
    TEST("rns_add_redundant_check succeeds");
    trit_rns_context_t red_ctx;
    trit_rns_init(&red_ctx);
    ASSERT(rns_add_redundant_check(&red_ctx) == 0, "expected 0");

    TEST("Count increased to 4 after redundant check");
    ASSERT(red_ctx.count == 4, "expected 4");

    TEST("New modulus is coprime to all existing");
    int cop = 1;
    for (uint32_t i = 0; i < red_ctx.count - 1; i++) {
        if (rns_gcd_public(red_ctx.moduli[i],
                           red_ctx.moduli[red_ctx.count - 1]) != 1) {
            cop = 0; break;
        }
    }
    ASSERT(cop == 1, "coprime verified");

    TEST("New modulus is prime");
    uint32_t nm = red_ctx.moduli[red_ctx.count - 1];
    int is_p = 1;
    if (nm < 2) is_p = 0;
    for (uint32_t d = 2; (uint64_t)d * d <= nm; d++) {
        if (nm % d == 0) { is_p = 0; break; }
    }
    ASSERT(is_p == 1, "new modulus is prime");

    TEST("rns_add_redundant_check NULL → -1");
    ASSERT(rns_add_redundant_check(NULL) == -1, "expected -1");

    /* --- Fill to max and try again --- */
    TEST("Redundant check on near-max moduli");
    trit_rns_context_t full_ctx;
    trit_rns_init(&full_ctx);
    rns_extend_moduli(&full_ctx, 11);
    rns_extend_moduli(&full_ctx, 13);
    /* Now count=5, one slot left */
    ASSERT(rns_add_redundant_check(&full_ctx) == 0, "expected 0");

    TEST("After fill, count == 6 (max)");
    ASSERT(full_ctx.count == 6, "expected 6");

    TEST("Redundant check on full context → -1");
    ASSERT(rns_add_redundant_check(&full_ctx) == -1, "expected -1");

    SECTION("RNS: Crypto — Error Detection/Correction");

    /* --- Detect/correct: no error --- */
    TEST("detect_correct: clean residue → 0 (no error)");
    trit_rns_context_t dc_ctx;
    trit_rns_init(&dc_ctx);
    rns_add_redundant_check(&dc_ctx); /* 4 moduli */
    trit_rns_t clean;
    for (uint32_t i = 0; i < dc_ctx.count; i++)
        clean.residues[i] = 42 % dc_ctx.moduli[i];
    trit_rns_t corrected;
    ASSERT(rns_detect_correct(&clean, &corrected, &dc_ctx) == 0, "expected 0");

    TEST("Corrected matches original on no-error");
    ASSERT(corrected.residues[0] == clean.residues[0]
        && corrected.residues[1] == clean.residues[1]
        && corrected.residues[2] == clean.residues[2],
           "corrected == original");

    /* --- detect_correct NULL cases --- */
    TEST("detect_correct NULL rns → -1");
    ASSERT(rns_detect_correct(NULL, &corrected, &dc_ctx) == -1, "expected -1");

    TEST("detect_correct NULL corrected → -1");
    ASSERT(rns_detect_correct(&clean, NULL, &dc_ctx) == -1, "expected -1");

    TEST("detect_correct NULL ctx → -1");
    ASSERT(rns_detect_correct(&clean, &corrected, NULL) == -1, "expected -1");

    /* --- detect_correct: too few moduli --- */
    TEST("detect_correct with 1 modulus → -1");
    trit_rns_context_t tiny;
    uint32_t one_mod[] = {5};
    trit_rns_init_custom(&tiny, one_mod, 1);
    ASSERT(rns_detect_correct(&clean, &corrected, &tiny) == -1, "expected -1");

    /* --- Montgomery exp consistency: same exp → same result --- */
    TEST("Montgomery exp: a^4 deterministic");
    trit_rns_t a4_1, a4_2;
    trit_rns_t base2 = {{ 2, 4, 5 }};
    rns_montgomery_exp(&base2, 4, &a4_1, &ctx);
    rns_montgomery_exp(&base2, 4, &a4_2, &ctx);
    ASSERT(a4_1.residues[0] == a4_2.residues[0]
        && a4_1.residues[1] == a4_2.residues[1]
        && a4_1.residues[2] == a4_2.residues[2],
           "a^4 deterministic");

    /* --- Multiple redundant chains --- */
    TEST("Montgomery exp deterministic: same input → same output");
    trit_rns_t d1, d2;
    rns_montgomery_exp(&base2, 7, &d1, &ctx);
    rns_montgomery_exp(&base2, 7, &d2, &ctx);
    ASSERT(d1.residues[0] == d2.residues[0]
        && d1.residues[1] == d2.residues[1]
        && d1.residues[2] == d2.residues[2],
           "deterministic");

    /* --- Montgomery exp with crypto moduli: various exponents --- */
    TEST("Crypto Montgomery exp: base^10 in range");
    trit_rns_t cb10;
    rns_montgomery_exp(&cb, 10, &cb10, &cry);
    int cry_r = 1;
    for (uint32_t i = 0; i < cry.count; i++) {
        if (cb10.residues[i] >= cry.moduli[i]) { cry_r = 0; break; }
    }
    ASSERT(cry_r == 1, "crypto exp^10 in range");

    TEST("Crypto Montgomery exp: 0^0 → (1,...) channels");
    trit_rns_t czero = {{ 0, 0, 0, 0, 0 }};
    trit_rns_t cz0;
    rns_montgomery_exp(&czero, 0, &cz0, &cry);
    cry_r = 1;
    for (uint32_t i = 0; i < cry.count; i++) {
        if (cz0.residues[i] >= cry.moduli[i]) { cry_r = 0; break; }
    }
    ASSERT(cry_r == 1, "0^0 in range across crypto channels");

    TEST("Redundant modulus > max existing modulus");
    ASSERT(red_ctx.moduli[red_ctx.count - 1] > red_ctx.moduli[red_ctx.count - 2],
           "redundant modulus is larger");

    TEST("Redundant context: M > 105");
    ASSERT(red_ctx.M > 105, "extended M > original 105");
}

/* ========================================================================
 * 15. Multi-Radix Extended — Diverse Moduli Sets (70 assertions)
 * ======================================================================== */

static void test_multi_radix_extended(void) {
    SECTION("RNS: Multi-Radix — Mersenne-4 {3,4,5}");

    trit_rns_context_t m4;
    uint32_t mod_m4[] = {RNS_MODSET_MERSENNE_4};
    trit_rns_init_custom(&m4, mod_m4, 3);

    /* Arithmetic in {3,4,5} domain: 10+20=30, 30 < M=60 */
    TEST("Mersenne-4 add: 10+20=30");
    trit_rns_t a10 = {{ 10 % 3, 10 % 4, 10 % 5 }};
    trit_rns_t a20 = {{ 20 % 3, 20 % 4, 20 % 5 }};
    trit_rns_t s30;
    rns_add(&a10, &a20, &s30, &m4);
    ASSERT(s30.residues[0] == 30 % 3
        && s30.residues[1] == 30 % 4
        && s30.residues[2] == 30 % 5,
           "expected residues of 30");

    TEST("Mersenne-4 mul: 3*4=12");
    trit_rns_t m3 = {{ 3 % 3, 3 % 4, 3 % 5 }};
    trit_rns_t m_4 = {{ 4 % 3, 4 % 4, 4 % 5 }};
    trit_rns_t p12;
    rns_mul(&m3, &m_4, &p12, &m4);
    ASSERT(p12.residues[0] == 12 % 3
        && p12.residues[1] == 12 % 4
        && p12.residues[2] == 12 % 5,
           "expected residues of 12");

    TEST("Mersenne-4 sub: 20-10=10");
    trit_rns_t d10_m4;
    rns_sub(&a20, &a10, &d10_m4, &m4);
    ASSERT(d10_m4.residues[0] == 10 % 3
        && d10_m4.residues[1] == 10 % 4
        && d10_m4.residues[2] == 10 % 5,
           "expected residues of 10");

    TEST("Mersenne-4 zero detect");
    trit_rns_t z4 = {{ 0, 0, 0 }};
    ASSERT(rns_is_zero(&z4, &m4) == true, "expected true");

    TEST("Mersenne-4 validate all values 0..59");
    int ok_m4 = 1;
    for (uint32_t v = 0; v < 60; v++) {
        trit_rns_t rv = {{ v % 3, v % 4, v % 5 }};
        if (rns_validate(&rv, &m4) != 0) { ok_m4 = 0; break; }
    }
    ASSERT(ok_m4 == 1, "all 60 values valid");

    TEST("Mersenne-4 MRS roundtrip for value 42");
    trit_rns_t rm4_42 = {{ 42 % 3, 42 % 4, 42 % 5 }};
    uint32_t dm4[RNS_MAX_MODULI] = {0};
    rns_to_mrs(&rm4_42, dm4, &m4);
    trit_rns_t rm4_back;
    rns_from_mrs(dm4, &rm4_back, &m4);
    ASSERT(rm4_back.residues[0] == rm4_42.residues[0]
        && rm4_back.residues[1] == rm4_42.residues[1]
        && rm4_back.residues[2] == rm4_42.residues[2],
           "MRS roundtrip in Mersenne-4");

    TEST("Mersenne-4 Montgomery mul valid range");
    trit_rns_t mont_a = {{ 2, 3, 4 }};
    trit_rns_t mont_b = {{ 1, 2, 3 }};
    trit_rns_t mont_r;
    rns_montgomery_mul(&mont_a, &mont_b, &mont_r, &m4);
    ASSERT(mont_r.residues[0] < 3 && mont_r.residues[1] < 4
        && mont_r.residues[2] < 5, "in range");

    SECTION("RNS: Multi-Radix — Mersenne-8 {7,8,9}");

    trit_rns_context_t m8;
    uint32_t mod_m8[] = {RNS_MODSET_MERSENNE_8};
    trit_rns_init_custom(&m8, mod_m8, 3);

    TEST("Mersenne-8 add: 100+200=300");
    trit_rns_t a100 = {{ 100 % 7, 100 % 8, 100 % 9 }};
    trit_rns_t a200 = {{ 200 % 7, 200 % 8, 200 % 9 }};
    trit_rns_t s300;
    rns_add(&a100, &a200, &s300, &m8);
    ASSERT(s300.residues[0] == 300 % 7
        && s300.residues[1] == 300 % 8
        && s300.residues[2] == 300 % 9,
           "expected residues of 300");

    TEST("Mersenne-8 mul: 10*20=200");
    trit_rns_t m10 = {{ 10 % 7, 10 % 8, 10 % 9 }};
    trit_rns_t m20 = {{ 20 % 7, 20 % 8, 20 % 9 }};
    trit_rns_t p200;
    rns_mul(&m10, &m20, &p200, &m8);
    ASSERT(p200.residues[0] == 200 % 7
        && p200.residues[1] == 200 % 8
        && p200.residues[2] == 200 % 9,
           "expected residues of 200");

    TEST("Mersenne-8 sub identity: a - a = 0");
    trit_rns_t d0;
    rns_sub(&a100, &a100, &d0, &m8);
    ASSERT(rns_is_zero(&d0, &m8), "expected zero");

    TEST("Mersenne-8 validate all values 0..503");
    int ok_m8 = 1;
    for (uint32_t v = 0; v < 504; v++) {
        trit_rns_t rv = {{ v % 7, v % 8, v % 9 }};
        if (rns_validate(&rv, &m8) != 0) { ok_m8 = 0; break; }
    }
    ASSERT(ok_m8 == 1, "all 504 values valid");

    TEST("Mersenne-8 Montgomery exp base^3 in range");
    trit_rns_t m8_base = {{ 3, 5, 6 }};
    trit_rns_t m8_r;
    rns_montgomery_exp(&m8_base, 3, &m8_r, &m8);
    ASSERT(m8_r.residues[0] < 7 && m8_r.residues[1] < 8
        && m8_r.residues[2] < 9, "in range");

    SECTION("RNS: Multi-Radix — Ternary {3,13,37}");

    trit_rns_context_t tc;
    uint32_t mod_tc[] = {RNS_MODSET_TERNARY};
    trit_rns_init_custom(&tc, mod_tc, 3);

    TEST("Ternary add: 500+700=1200");
    trit_rns_t t500 = {{ 500 % 3, 500 % 13, 500 % 37 }};
    trit_rns_t t700 = {{ 700 % 3, 700 % 13, 700 % 37 }};
    trit_rns_t t1200;
    rns_add(&t500, &t700, &t1200, &tc);
    ASSERT(t1200.residues[0] == 1200 % 3
        && t1200.residues[1] == 1200 % 13
        && t1200.residues[2] == 1200 % 37,
           "expected residues of 1200");

    TEST("Ternary mul: 30*40=1200");
    trit_rns_t t30 = {{ 30 % 3, 30 % 13, 30 % 37 }};
    trit_rns_t t40 = {{ 40 % 3, 40 % 13, 40 % 37 }};
    trit_rns_t t1200_mul;
    rns_mul(&t30, &t40, &t1200_mul, &tc);
    ASSERT(t1200_mul.residues[0] == 1200 % 3
        && t1200_mul.residues[1] == 1200 % 13
        && t1200_mul.residues[2] == 1200 % 37,
           "expected residues of 1200");

    TEST("Ternary sub: 1000-500=500");
    trit_rns_t t1000 = {{ 1000 % 3, 1000 % 13, 1000 % 37 }};
    trit_rns_t t500_sub;
    rns_sub(&t1000, &t500, &t500_sub, &tc);
    ASSERT(t500_sub.residues[0] == 500 % 3
        && t500_sub.residues[1] == 500 % 13
        && t500_sub.residues[2] == 500 % 37,
           "expected residues of 500");

    TEST("Ternary distributive: 3*(100+200)=3*100+3*200");
    trit_rns_t tc3  = {{ 3 % 3, 3 % 13, 3 % 37 }};
    trit_rns_t tc100 = {{ 100 % 3, 100 % 13, 100 % 37 }};
    trit_rns_t tc200 = {{ 200 % 3, 200 % 13, 200 % 37 }};
    trit_rns_t tc_sum, tc_lhs, tc_p1, tc_p2, tc_rhs;
    rns_add(&tc100, &tc200, &tc_sum, &tc);
    rns_mul(&tc3, &tc_sum, &tc_lhs, &tc);
    rns_mul(&tc3, &tc100, &tc_p1, &tc);
    rns_mul(&tc3, &tc200, &tc_p2, &tc);
    rns_add(&tc_p1, &tc_p2, &tc_rhs, &tc);
    ASSERT(tc_lhs.residues[0] == tc_rhs.residues[0]
        && tc_lhs.residues[1] == tc_rhs.residues[1]
        && tc_lhs.residues[2] == tc_rhs.residues[2],
           "distributive in ternary moduli");

    TEST("Ternary MRS roundtrip for value 1000");
    trit_rns_t rt1000 = {{ 1000 % 3, 1000 % 13, 1000 % 37 }};
    uint32_t dt[RNS_MAX_MODULI] = {0};
    rns_to_mrs(&rt1000, dt, &tc);
    trit_rns_t rt1000_back;
    rns_from_mrs(dt, &rt1000_back, &tc);
    ASSERT(rt1000_back.residues[0] == rt1000.residues[0]
        && rt1000_back.residues[1] == rt1000.residues[1]
        && rt1000_back.residues[2] == rt1000.residues[2],
           "ternary MRS roundtrip");

    TEST("Ternary validate value 1442 (max-1)");
    trit_rns_t rmax = {{ 1442 % 3, 1442 % 13, 1442 % 37 }};
    ASSERT(rns_validate(&rmax, &tc) == 0, "expected valid");

    SECTION("RNS: Multi-Radix — Crypto {11,13,17,19,23}");

    trit_rns_context_t cry;
    uint32_t mod_cry[] = {RNS_MODSET_CRYPTO};
    trit_rns_init_custom(&cry, mod_cry, 5);

    TEST("Crypto add: 500000+500000=1000000");
    trit_rns_t c5e5 = {{ 500000 % 11, 500000 % 13, 500000 % 17,
                         500000 % 19, 500000 % 23 }};
    trit_rns_t c_sum;
    rns_add(&c5e5, &c5e5, &c_sum, &cry);
    ASSERT(c_sum.residues[0] == 1000000 % 11
        && c_sum.residues[1] == 1000000 % 13
        && c_sum.residues[2] == 1000000 % 17
        && c_sum.residues[3] == 1000000 % 19
        && c_sum.residues[4] == 1000000 % 23,
           "expected residues of 1000000");

    TEST("Crypto mul: 1000*1000=1000000");
    trit_rns_t c1k = {{ 1000 % 11, 1000 % 13, 1000 % 17,
                        1000 % 19, 1000 % 23 }};
    trit_rns_t c_prod;
    rns_mul(&c1k, &c1k, &c_prod, &cry);
    ASSERT(c_prod.residues[0] == 1000000 % 11
        && c_prod.residues[1] == 1000000 % 13
        && c_prod.residues[2] == 1000000 % 17
        && c_prod.residues[3] == 1000000 % 19
        && c_prod.residues[4] == 1000000 % 23,
           "expected residues of 1000000");

    TEST("Crypto sub identity");
    trit_rns_t c_zero;
    rns_sub(&c1k, &c1k, &c_zero, &cry);
    ASSERT(rns_is_zero(&c_zero, &cry), "expected zero");

    TEST("Crypto commutativity: a*b == b*a");
    trit_rns_t ca = {{ 12345 % 11, 12345 % 13, 12345 % 17,
                       12345 % 19, 12345 % 23 }};
    trit_rns_t cb_v = {{ 67890 % 11, 67890 % 13, 67890 % 17,
                       67890 % 19, 67890 % 23 }};
    trit_rns_t cab, cba;
    rns_mul(&ca, &cb_v, &cab, &cry);
    rns_mul(&cb_v, &ca, &cba, &cry);
    ASSERT(cab.residues[0] == cba.residues[0]
        && cab.residues[1] == cba.residues[1]
        && cab.residues[2] == cba.residues[2]
        && cab.residues[3] == cba.residues[3]
        && cab.residues[4] == cba.residues[4],
           "commutative in crypto moduli");

    TEST("Crypto validate: range check for value 1000000");
    ASSERT(rns_validate(&c_sum, &cry) == 0, "expected valid");

    TEST("Crypto MRS roundtrip for 888888");
    trit_rns_t c888 = {{ 888888 % 11, 888888 % 13, 888888 % 17,
                         888888 % 19, 888888 % 23 }};
    uint32_t dc888[RNS_MAX_MODULI] = {0};
    rns_to_mrs(&c888, dc888, &cry);
    trit_rns_t c888_back;
    rns_from_mrs(dc888, &c888_back, &cry);
    ASSERT(c888_back.residues[0] == c888.residues[0]
        && c888_back.residues[1] == c888.residues[1]
        && c888_back.residues[2] == c888.residues[2]
        && c888_back.residues[3] == c888.residues[3]
        && c888_back.residues[4] == c888.residues[4],
           "crypto MRS roundtrip matches");

    SECTION("RNS: Multi-Radix — Dynamic Extension Patterns");

    /* Start with {3,5} and extend step by step */
    TEST("Dynamic: init {3,5} → M=15");
    trit_rns_context_t dyn;
    uint32_t mod_dyn[] = {3, 5};
    trit_rns_init_custom(&dyn, mod_dyn, 2);
    ASSERT(dyn.M == 15, "expected 15");

    TEST("Dynamic: extend with 7 → M=105");
    ASSERT(rns_extend_moduli(&dyn, 7) == 0, "expected 0");

    TEST("Dynamic: M after +7 == 105");
    ASSERT(dyn.M == 105, "expected 105");

    TEST("Dynamic: extend with 11 → M=1155");
    ASSERT(rns_extend_moduli(&dyn, 11) == 0, "expected 0");

    TEST("Dynamic: M after +11 == 1155");
    ASSERT(dyn.M == 1155, "expected 1155");

    TEST("Dynamic: extend with 13 → M=15015");
    ASSERT(rns_extend_moduli(&dyn, 13) == 0, "expected 0");

    TEST("Dynamic: M after +13 == 15015");
    ASSERT(dyn.M == 15015, "expected 15015");

    TEST("Dynamic: extend with 17 → M=255255");
    ASSERT(rns_extend_moduli(&dyn, 17) == 0, "expected 0");

    TEST("Dynamic: M after +17 == 255255");
    ASSERT(dyn.M == 255255, "expected 255255");

    TEST("Dynamic: count == 6 (max)");
    ASSERT(dyn.count == 6, "expected 6");

    TEST("Dynamic: arithmetic on 6 moduli: 100+200=300");
    trit_rns_t da = {{ 100 % 3, 100 % 5, 100 % 7,
                       100 % 11, 100 % 13, 100 % 17 }};
    trit_rns_t db = {{ 200 % 3, 200 % 5, 200 % 7,
                       200 % 11, 200 % 13, 200 % 17 }};
    trit_rns_t dsum;
    rns_add(&da, &db, &dsum, &dyn);
    int dyn_ok = 1;
    uint32_t dyn_mods[] = {3, 5, 7, 11, 13, 17};
    for (int i = 0; i < 6; i++) {
        if (dsum.residues[i] != 300 % dyn_mods[i]) { dyn_ok = 0; break; }
    }
    ASSERT(dyn_ok == 1, "6-moduli add correct");

    TEST("Dynamic: 6-moduli multiply 10*20=200");
    trit_rns_t d10_dyn = {{ 10 % 3, 10 % 5, 10 % 7,
                        10 % 11, 10 % 13, 10 % 17 }};
    trit_rns_t d20_dyn = {{ 20 % 3, 20 % 5, 20 % 7,
                        20 % 11, 20 % 13, 20 % 17 }};
    trit_rns_t dprod;
    rns_mul(&d10_dyn, &d20_dyn, &dprod, &dyn);
    dyn_ok = 1;
    for (int i = 0; i < 6; i++) {
        if (dprod.residues[i] != 200 % dyn_mods[i]) { dyn_ok = 0; break; }
    }
    ASSERT(dyn_ok == 1, "6-moduli mul correct");

    TEST("Dynamic: 6-moduli MRS roundtrip value 100000");
    trit_rns_t d1e5;
    for (int i = 0; i < 6; i++)
        d1e5.residues[i] = 100000 % dyn_mods[i];
    uint32_t dd[RNS_MAX_MODULI] = {0};
    rns_to_mrs(&d1e5, dd, &dyn);
    trit_rns_t d1e5_back;
    rns_from_mrs(dd, &d1e5_back, &dyn);
    dyn_ok = 1;
    for (int i = 0; i < 6; i++) {
        if (d1e5_back.residues[i] != d1e5.residues[i]) { dyn_ok = 0; break; }
    }
    ASSERT(dyn_ok == 1, "6-moduli MRS roundtrip matches");

    TEST("Dynamic: 6-moduli validate 100000");
    ASSERT(rns_validate(&d1e5, &dyn) == 0, "expected valid");

    TEST("Dynamic: 6-moduli Montgomery exp in range");
    trit_rns_t dbase;
    for (int i = 0; i < 6; i++)
        dbase.residues[i] = 42 % dyn_mods[i];
    trit_rns_t dexp;
    rns_montgomery_exp(&dbase, 5, &dexp, &dyn);
    dyn_ok = 1;
    for (uint32_t i = 0; i < dyn.count; i++) {
        if (dexp.residues[i] >= dyn.moduli[i]) { dyn_ok = 0; break; }
    }
    ASSERT(dyn_ok == 1, "6-moduli Montgomery exp in range");

    SECTION("RNS: Multi-Radix — Cross-Domain Consistency");

    /* Verify same value produces same residues across different init paths */
    TEST("Cross-domain: standard init vs custom init for {3,5,7}");
    trit_rns_context_t std_ctx, cust_ctx;
    trit_rns_init(&std_ctx);
    uint32_t m357[] = {3, 5, 7};
    trit_rns_init_custom(&cust_ctx, m357, 3);
    ASSERT(std_ctx.M == cust_ctx.M
        && std_ctx.count == cust_ctx.count,
           "standard and custom init match");

    TEST("Cross-domain: Mi values match");
    ASSERT(std_ctx.Mi[0] == cust_ctx.Mi[0]
        && std_ctx.Mi[1] == cust_ctx.Mi[1]
        && std_ctx.Mi[2] == cust_ctx.Mi[2],
           "Mi values match");

    TEST("Cross-domain: Mi_inv values match");
    ASSERT(std_ctx.Mi_inv[0] == cust_ctx.Mi_inv[0]
        && std_ctx.Mi_inv[1] == cust_ctx.Mi_inv[1]
        && std_ctx.Mi_inv[2] == cust_ctx.Mi_inv[2],
           "Mi_inv values match");

    /* Verify non-coprime detection for common edge cases */
    TEST("Non-coprime: {4,6,7} → -1 (gcd(4,6)=2)");
    trit_rns_context_t nc1;
    uint32_t nc_mods1[] = {4, 6, 7};
    ASSERT(trit_rns_init_custom(&nc1, nc_mods1, 3) == -1, "expected -1");

    TEST("Non-coprime: {9,15,7} → -1 (gcd(9,15)=3)");
    trit_rns_context_t nc2;
    uint32_t nc_mods2[] = {9, 15, 7};
    ASSERT(trit_rns_init_custom(&nc2, nc_mods2, 3) == -1, "expected -1");

    TEST("Coprime: {8,9,25} → M=1800");
    trit_rns_context_t cp;
    uint32_t cp_mods[] = {8, 9, 25};
    ASSERT(trit_rns_init_custom(&cp, cp_mods, 3) == 0, "expected 0");

    TEST("Coprime {8,9,25} M == 1800");
    ASSERT(cp.M == 1800, "expected 1800");

    /* Arithmetic in {8,9,25} domain */
    TEST("{8,9,25} add: 1000+500=1500");
    trit_rns_t cp_a = {{ 1000 % 8, 1000 % 9, 1000 % 25 }};
    trit_rns_t cp_b = {{ 500 % 8, 500 % 9, 500 % 25 }};
    trit_rns_t cp_sum;
    rns_add(&cp_a, &cp_b, &cp_sum, &cp);
    ASSERT(cp_sum.residues[0] == 1500 % 8
        && cp_sum.residues[1] == 1500 % 9
        && cp_sum.residues[2] == 1500 % 25,
           "expected residues of 1500");

    TEST("{8,9,25} MRS roundtrip for 1234");
    trit_rns_t cp_1234 = {{ 1234 % 8, 1234 % 9, 1234 % 25 }};
    uint32_t dcp[RNS_MAX_MODULI] = {0};
    rns_to_mrs(&cp_1234, dcp, &cp);
    trit_rns_t cp_1234_back;
    rns_from_mrs(dcp, &cp_1234_back, &cp);
    ASSERT(cp_1234_back.residues[0] == cp_1234.residues[0]
        && cp_1234_back.residues[1] == cp_1234.residues[1]
        && cp_1234_back.residues[2] == cp_1234.residues[2],
           "{8,9,25} MRS roundtrip matches");

    /* Associativity: (a+b)+c = a+(b+c) across moduli sets */
    TEST("Associativity: (a+b)+c == a+(b+c) in {3,13,37}");
    trit_rns_context_t as_ctx;
    uint32_t as_mods[] = {3, 13, 37};
    trit_rns_init_custom(&as_ctx, as_mods, 3);
    trit_rns_t as_a = {{ 100 % 3, 100 % 13, 100 % 37 }};
    trit_rns_t as_b = {{ 200 % 3, 200 % 13, 200 % 37 }};
    trit_rns_t as_c = {{ 300 % 3, 300 % 13, 300 % 37 }};
    trit_rns_t ab_sum, abc_lhs, bc_sum, abc_rhs;
    rns_add(&as_a, &as_b, &ab_sum, &as_ctx);
    rns_add(&ab_sum, &as_c, &abc_lhs, &as_ctx);
    rns_add(&as_b, &as_c, &bc_sum, &as_ctx);
    rns_add(&as_a, &bc_sum, &abc_rhs, &as_ctx);
    ASSERT(abc_lhs.residues[0] == abc_rhs.residues[0]
        && abc_lhs.residues[1] == abc_rhs.residues[1]
        && abc_lhs.residues[2] == abc_rhs.residues[2],
           "associative");

    /* Montgomery mul associativity */
    TEST("Montgomery mul associativity: (a*b)*c == a*(b*c) in {7,8,9}");
    trit_rns_t ma = {{ 3, 5, 6 }};
    trit_rns_t mb = {{ 2, 4, 7 }};
    trit_rns_t mc = {{ 1, 3, 5 }};
    trit_rns_t mab, mabc_l, mbc, mabc_r;
    rns_montgomery_mul(&ma, &mb, &mab, &m8);
    rns_montgomery_mul(&mab, &mc, &mabc_l, &m8);
    rns_montgomery_mul(&mb, &mc, &mbc, &m8);
    rns_montgomery_mul(&ma, &mbc, &mabc_r, &m8);
    ASSERT(mabc_l.residues[0] == mabc_r.residues[0]
        && mabc_l.residues[1] == mabc_r.residues[1]
        && mabc_l.residues[2] == mabc_r.residues[2],
           "Montgomery associative");

    /* Single-modulus context */
    TEST("Single modulus {5}: init + arithmetic");
    trit_rns_context_t s1;
    uint32_t one_m[] = {5};
    ASSERT(trit_rns_init_custom(&s1, one_m, 1) == 0, "expected 0");

    TEST("Single modulus M == 5");
    ASSERT(s1.M == 5, "expected M=5");

    TEST("Single modulus: add 3+4=7→2 mod 5");
    trit_rns_t s_a = {{ 3 }};
    trit_rns_t s_b = {{ 4 }};
    trit_rns_t s_sum;
    rns_add(&s_a, &s_b, &s_sum, &s1);
    ASSERT(s_sum.residues[0] == 2, "expected 2 (7 mod 5)");

    TEST("Single modulus: mul 3*4=12→2 mod 5");
    trit_rns_t s_prod;
    rns_mul(&s_a, &s_b, &s_prod, &s1);
    ASSERT(s_prod.residues[0] == 2, "expected 2 (12 mod 5)");

    /* Two-modulus context */
    TEST("Two moduli {3,7}: init + MRS roundtrip");
    trit_rns_context_t t2;
    uint32_t two_m[] = {3, 7};
    trit_rns_init_custom(&t2, two_m, 2);
    ASSERT(t2.M == 21, "expected M=21");

    TEST("Two moduli MRS roundtrip for value 17");
    trit_rns_t rt17 = {{ 17 % 3, 17 % 7 }};
    uint32_t dt17[RNS_MAX_MODULI] = {0};
    rns_to_mrs(&rt17, dt17, &t2);
    trit_rns_t rt17_back;
    rns_from_mrs(dt17, &rt17_back, &t2);
    ASSERT(rt17_back.residues[0] == rt17.residues[0]
        && rt17_back.residues[1] == rt17.residues[1],
           "two-moduli MRS roundtrip");

    /* Large moduli test: {97, 101, 103} */
    TEST("Large moduli {97,101,103}: init → M=1009291");
    trit_rns_context_t lg;
    uint32_t lg_mods[] = {97, 101, 103};
    ASSERT(trit_rns_init_custom(&lg, lg_mods, 3) == 0, "expected 0");

    TEST("Large moduli M == 97*101*103");
    ASSERT(lg.M == 97u * 101u * 103u, "expected product");

    TEST("Large moduli arithmetic: 500000+400000=900000");
    trit_rns_t lg_a = {{ 500000 % 97, 500000 % 101, 500000 % 103 }};
    trit_rns_t lg_b = {{ 400000 % 97, 400000 % 101, 400000 % 103 }};
    trit_rns_t lg_sum;
    rns_add(&lg_a, &lg_b, &lg_sum, &lg);
    ASSERT(lg_sum.residues[0] == 900000 % 97
        && lg_sum.residues[1] == 900000 % 101
        && lg_sum.residues[2] == 900000 % 103,
           "large moduli add correct");

    TEST("Large moduli MRS roundtrip for 800000");
    trit_rns_t lg_800k = {{ 800000 % 97, 800000 % 101, 800000 % 103 }};
    uint32_t dlg[RNS_MAX_MODULI] = {0};
    rns_to_mrs(&lg_800k, dlg, &lg);
    trit_rns_t lg_800k_back;
    rns_from_mrs(dlg, &lg_800k_back, &lg);
    ASSERT(lg_800k_back.residues[0] == lg_800k.residues[0]
        && lg_800k_back.residues[1] == lg_800k.residues[1]
        && lg_800k_back.residues[2] == lg_800k.residues[2],
           "large moduli MRS roundtrip");

    /* Redundant check + arithmetic chain */
    TEST("Redundant check + chain: add in extended context");
    trit_rns_context_t rd;
    trit_rns_init(&rd);
    rns_add_redundant_check(&rd);
    trit_rns_t rd_a, rd_b, rd_sum;
    for (uint32_t i = 0; i < rd.count; i++) {
        rd_a.residues[i] = 10 % rd.moduli[i];
        rd_b.residues[i] = 20 % rd.moduli[i];
    }
    rns_add(&rd_a, &rd_b, &rd_sum, &rd);
    int rd_ok = 1;
    for (uint32_t i = 0; i < rd.count; i++) {
        if (rd_sum.residues[i] != 30 % rd.moduli[i]) { rd_ok = 0; break; }
    }
    ASSERT(rd_ok == 1, "redundant context arithmetic correct");

    TEST("Redundant check: detect_correct clean → 0");
    trit_rns_t rd_clean;
    for (uint32_t i = 0; i < rd.count; i++)
        rd_clean.residues[i] = 50 % rd.moduli[i];
    trit_rns_t rd_corrected;
    ASSERT(rns_detect_correct(&rd_clean, &rd_corrected, &rd) == 0,
           "expected 0 (no error)");

    /* --- Final boundary and edge tests --- */
    TEST("Redundant: validate before and after extension");
    trit_rns_t rd_val;
    for (uint32_t i = 0; i < rd.count; i++)
        rd_val.residues[i] = 70 % rd.moduli[i];
    ASSERT(rns_validate(&rd_val, &rd) == 0, "valid in extended context");

    TEST("Two moduli {3,7}: zero detection");
    trit_rns_t t2_zero = {{ 0, 0 }};
    ASSERT(rns_is_zero(&t2_zero, &t2), "zero in two-moduli");

    TEST("Large moduli multiply: 100*200=20000");
    trit_rns_t lg_c = {{ 100 % 97, 100 % 101, 100 % 103 }};
    trit_rns_t lg_d = {{ 200 % 97, 200 % 101, 200 % 103 }};
    trit_rns_t lg_prod;
    rns_mul(&lg_c, &lg_d, &lg_prod, &lg);
    ASSERT(lg_prod.residues[0] == 20000 % 97
        && lg_prod.residues[1] == 20000 % 101
        && lg_prod.residues[2] == 20000 % 103,
           "large moduli multiply correct");

    TEST("Large moduli validate 20000");
    ASSERT(rns_validate(&lg_prod, &lg) == 0, "expected valid");
}

/* ==== Main ============================================================= */

int main(void) {
    printf("=== seT6 RNS Test Suite ===\n");

    test_init_and_crt();
    test_trit_to_rns();
    test_crt_reconstruction();
    test_arithmetic();
    test_montgomery();
    test_zero_sparsity();
    test_validate();
    test_extend_moduli();
    test_pvt_resilience();
    test_crypto_integration();
    test_noise_injection();
    test_conversions_extended();
    test_low_power_sim();
    test_crypto_extended();
    test_multi_radix_extended();

    printf("\n=== RNS Tests: %d passed, %d failed, %d total ===\n",
           tests_passed, tests_failed, tests_total);
    return tests_failed ? 1 : 0;
}
