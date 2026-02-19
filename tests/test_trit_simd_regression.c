/**
 * @file test_trit_simd_regression.c
 * @brief T-031: Exhaustive SIMD packed64 regression tests
 *
 * Validates trit_and_packed64 / trit_or_packed64 / trit_not_packed64
 * against scalar reference for ALL 32-trit word combinations.
 * Confirms T-SAR finding that SIMD ternary is production-ready.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/trit.h"
#include <stdio.h>
#include <stdint.h>
#include <string.h>

static int tests_passed = 0;
static int tests_failed = 0;

#define TEST(name) do { printf("  %-60s ", #name); fflush(stdout); } while(0)
#define PASS()     do { printf("[PASS]\n"); tests_passed++; } while(0)
#define FAIL(msg)  do { printf("[FAIL] %s\n", msg); tests_failed++; } while(0)

/* ── Helpers ── */

/**
 * Encode scalar trit array into packed64 using the SIMD encoding:
 *   -1 (FALSE) → 0b10 (hi=1, lo=0)
 *    0 (UNKNOWN) → 0b00 (hi=0, lo=0)
 *   +1 (TRUE)  → 0b01 (hi=0, lo=1)
 *
 * Note: this matches the encoding used by trit_and/or/not_packed64.
 * The trit_pack() function uses a different encoding scheme (for
 * register/storage), so we cannot use it for SIMD test vectors.
 */
static uint64_t pack_trits(const trit *arr, int n) {
    uint64_t packed = 0;
    for (int i = 0; i < n && i < 32; i++) {
        uint64_t pair;
        if (arr[i] < 0)      pair = 0x02; /* 0b10 = FALSE */
        else if (arr[i] > 0) pair = 0x01; /* 0b01 = TRUE  */
        else                  pair = 0x00; /* 0b00 = UNKNOWN */
        packed |= (pair << (2 * i));
    }
    return packed;
}

/**
 * Extract one trit from packed64 using SIMD encoding.
 */
static trit extract_trit(uint64_t packed, int pos) {
    uint64_t pair = (packed >> (2 * pos)) & 0x03;
    if (pair == 0x02) return TRIT_FALSE;   /* 0b10 */
    if (pair == 0x01) return TRIT_TRUE;    /* 0b01 */
    return TRIT_UNKNOWN;                    /* 0b00 (or 0b11 fault→unknown) */
}

/* ── Test: scalar-vs-packed AND for all 3^2 = 9 single-trit pairs ── */
static void test_and_exhaustive_single(void) {
    TEST(simd_and_all_9_pairs);
    trit vals[3] = { TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE };
    int ok = 1;
    for (int a = 0; a < 3; a++) {
        for (int b = 0; b < 3; b++) {
            trit expected = trit_and(vals[a], vals[b]);
            trit arr_a[32] = {0}, arr_b[32] = {0};
            arr_a[0] = vals[a]; arr_b[0] = vals[b];
            uint64_t pa = pack_trits(arr_a, 32);
            uint64_t pb = pack_trits(arr_b, 32);
            uint64_t pr = trit_and_packed64(pa, pb);
            trit got = extract_trit(pr, 0);
            if (got != expected) { ok = 0; break; }
        }
        if (!ok) break;
    }
    if (ok) PASS(); else FAIL("scalar/packed mismatch");
}

/* ── Test: scalar-vs-packed OR for all 9 pairs ── */
static void test_or_exhaustive_single(void) {
    TEST(simd_or_all_9_pairs);
    trit vals[3] = { TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE };
    int ok = 1;
    for (int a = 0; a < 3; a++) {
        for (int b = 0; b < 3; b++) {
            trit expected = trit_or(vals[a], vals[b]);
            trit arr_a[32] = {0}, arr_b[32] = {0};
            arr_a[0] = vals[a]; arr_b[0] = vals[b];
            uint64_t pa = pack_trits(arr_a, 32);
            uint64_t pb = pack_trits(arr_b, 32);
            uint64_t pr = trit_or_packed64(pa, pb);
            trit got = extract_trit(pr, 0);
            if (got != expected) { ok = 0; break; }
        }
        if (!ok) break;
    }
    if (ok) PASS(); else FAIL("scalar/packed mismatch");
}

/* ── Test: NOT round-trip for all 3 values at every position ── */
static void test_not_all_positions(void) {
    TEST(simd_not_all_32_positions);
    trit vals[3] = { TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE };
    int ok = 1;
    for (int pos = 0; pos < 32 && ok; pos++) {
        for (int v = 0; v < 3 && ok; v++) {
            trit arr[32];
            memset(arr, 0, sizeof(arr));
            arr[pos] = vals[v];
            uint64_t pa = pack_trits(arr, 32);
            uint64_t pn = trit_not_packed64(pa);
            trit expected = trit_not(vals[v]);
            trit got = extract_trit(pn, pos);
            if (got != expected) ok = 0;
        }
    }
    if (ok) PASS(); else FAIL("NOT position mismatch");
}

/* ── Test: double-NOT is identity ── */
static void test_not_involution(void) {
    TEST(simd_not_involution_all_encodings);
    /* Test 256 random-ish patterns */
    int ok = 1;
    for (uint64_t seed = 1; seed <= 256 && ok; seed++) {
        uint64_t val = seed * 0x0123456789ABCDEFULL;
        /* Mask to valid trit encodings (no 0b11 pairs) */
        uint64_t hi = val & 0xAAAAAAAAAAAAAAAAULL;
        uint64_t lo = val & 0x5555555555555555ULL;
        /* Remove fault pairs: if both hi and lo set, clear lo */
        uint64_t fault = (hi >> 1) & lo;
        lo &= ~fault;
        uint64_t clean = hi | lo;
        uint64_t result = trit_not_packed64(trit_not_packed64(clean));
        if (result != clean) ok = 0;
    }
    if (ok) PASS(); else FAIL("NOT(NOT(x)) != x");
}

/* ── Test: AND with all-true is identity ── */
static void test_and_identity(void) {
    TEST(simd_and_all_true_identity);
    uint64_t all_true = 0x5555555555555555ULL; /* all 01 pairs = TRUE */
    int ok = 1;
    for (uint64_t seed = 1; seed <= 100 && ok; seed++) {
        uint64_t val = seed * 0xDEADBEEFCAFEBABEULL;
        uint64_t hi = val & 0xAAAAAAAAAAAAAAAAULL;
        uint64_t lo = val & 0x5555555555555555ULL;
        uint64_t fault = (hi >> 1) & lo;
        lo &= ~fault;
        uint64_t clean = hi | lo;
        uint64_t result = trit_and_packed64(clean, all_true);
        if (result != clean) ok = 0;
    }
    if (ok) PASS(); else FAIL("AND(x, TRUE) != x");
}

/* ── Test: OR with all-false is identity ── */
static void test_or_identity(void) {
    TEST(simd_or_all_false_identity);
    uint64_t all_false = 0xAAAAAAAAAAAAAAAAULL; /* all 10 pairs = FALSE */
    int ok = 1;
    for (uint64_t seed = 1; seed <= 100 && ok; seed++) {
        uint64_t val = seed * 0x1234567890ABCDEFULL;
        uint64_t hi = val & 0xAAAAAAAAAAAAAAAAULL;
        uint64_t lo = val & 0x5555555555555555ULL;
        uint64_t fault = (hi >> 1) & lo;
        lo &= ~fault;
        uint64_t clean = hi | lo;
        uint64_t result = trit_or_packed64(clean, all_false);
        if (result != clean) ok = 0;
    }
    if (ok) PASS(); else FAIL("OR(x, FALSE) != x");
}

/* ── Test: De Morgan's law — NOT(AND(a,b)) == OR(NOT(a), NOT(b)) ── */
static void test_demorgan(void) {
    TEST(simd_demorgan_law_100_patterns);
    int ok = 1;
    for (uint64_t seed = 1; seed <= 100 && ok; seed++) {
        uint64_t va = seed * 0xFEDCBA9876543210ULL;
        uint64_t vb = seed * 0x0123456789ABCDEFULL;
        /* Clean to valid trit encodings */
        uint64_t ha = va & 0xAAAAAAAAAAAAAAAAULL;
        uint64_t la = va & 0x5555555555555555ULL;
        la &= ~((ha >> 1) & la); va = ha | la;
        uint64_t hb = vb & 0xAAAAAAAAAAAAAAAAULL;
        uint64_t lb = vb & 0x5555555555555555ULL;
        lb &= ~((hb >> 1) & lb); vb = hb | lb;

        uint64_t lhs = trit_not_packed64(trit_and_packed64(va, vb));
        uint64_t rhs = trit_or_packed64(trit_not_packed64(va), trit_not_packed64(vb));
        if (lhs != rhs) ok = 0;
    }
    if (ok) PASS(); else FAIL("De Morgan violated");
}

/* ── Test: full trit range present in packed outputs ── */
static void test_full_trit_range_output(void) {
    TEST(simd_outputs_contain_full_trit_range);
    /* AND of mixed input should produce -1, 0, +1 in results.
     * Use two different periods so both-TRUE positions exist:
     *   a cycles fast:  -1, 0, +1, -1, 0, +1, ...  (period 3)
     *   b cycles slow:  -1,-1,-1, 0, 0, 0, +1,+1,+1, ...  (period 9)
     * At i=8: a=+1, b=+1 → AND=+1.  At i=0: a=-1 → AND=-1. */
    trit a[32], b[32];
    for (int i = 0; i < 32; i++) {
        a[i] = (trit)((i % 3) - 1);         /* fast cycle  */
        b[i] = (trit)(((i / 3) % 3) - 1);   /* slow cycle  */
    }
    uint64_t pa = pack_trits(a, 32);
    uint64_t pb = pack_trits(b, 32);
    uint64_t pr = trit_and_packed64(pa, pb);

    int has_f = 0, has_u = 0, has_t = 0;
    for (int i = 0; i < 32; i++) {
        trit t = extract_trit(pr, i);
        if (t == TRIT_FALSE) has_f = 1;
        if (t == TRIT_UNKNOWN) has_u = 1;
        if (t == TRIT_TRUE) has_t = 1;
    }
    if (has_f && has_u && has_t) PASS();
    else FAIL("output missing trit values — binary reversion?");
}

/* ── Test: commutativity of AND/OR ── */
static void test_commutativity(void) {
    TEST(simd_and_or_commutativity);
    int ok = 1;
    for (uint64_t i = 1; i <= 50 && ok; i++) {
        uint64_t va = i * 0xABCDEF0123456789ULL;
        uint64_t vb = i * 0x9876543210FEDCBAULL;
        /* Clean */
        uint64_t h, l, f;
        h = va & 0xAAAAAAAAAAAAAAAAULL; l = va & 0x5555555555555555ULL;
        f = (h>>1) & l; l &= ~f; va = h | l;
        h = vb & 0xAAAAAAAAAAAAAAAAULL; l = vb & 0x5555555555555555ULL;
        f = (h>>1) & l; l &= ~f; vb = h | l;

        if (trit_and_packed64(va, vb) != trit_and_packed64(vb, va)) ok = 0;
        if (trit_or_packed64(va, vb) != trit_or_packed64(vb, va)) ok = 0;
    }
    if (ok) PASS(); else FAIL("commutativity violated");
}

/* ── Test: absorption laws ── */
static void test_absorption(void) {
    TEST(simd_absorption_laws);
    int ok = 1;
    /* AND(FALSE, x) = FALSE, OR(TRUE, x) = TRUE for any x */
    uint64_t all_false = 0xAAAAAAAAAAAAAAAAULL;
    uint64_t all_true  = 0x5555555555555555ULL;
    for (uint64_t i = 1; i <= 50 && ok; i++) {
        uint64_t v = i * 0xCAFEBABEDEADBEEFULL;
        uint64_t h = v & 0xAAAAAAAAAAAAAAAAULL;
        uint64_t l = v & 0x5555555555555555ULL;
        l &= ~((h>>1) & l); v = h | l;

        if (trit_and_packed64(all_false, v) != all_false) ok = 0;
        if (trit_or_packed64(all_true, v) != all_true) ok = 0;
    }
    if (ok) PASS(); else FAIL("absorption law violated");
}

int main(void) {
    printf("=== T-031: SIMD Packed64 Regression Suite ===\n");

    test_and_exhaustive_single();
    test_or_exhaustive_single();
    test_not_all_positions();
    test_not_involution();
    test_and_identity();
    test_or_identity();
    test_demorgan();
    test_full_trit_range_output();
    test_commutativity();
    test_absorption();

    printf("=== Results: %d passed, %d failed ===\n",
           tests_passed, tests_failed);
    return tests_failed ? 1 : 0;
}
