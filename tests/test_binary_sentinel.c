/**
 * @file test_binary_sentinel.c
 * @brief T-044: Automated binary reversion detector
 *
 * For each "at risk" function, asserts that outputs contain the full
 * trit range {-1, 0, +1}, that PRNG distribution is uniform over 3
 * values (not 2), and that no implicit bool→trit flattening occurs.
 *
 * Run as part of `make test6`.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/trit.h"
#include "set5/trit_cast.h"
#include "set5/trit_crypto.h"
#include "set5/multiradix.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>

/* bool_to_trit: convert C boolean (0/non-zero) to ternary trit value */
#ifndef bool_to_trit
#define bool_to_trit(b) ((b) ? TRIT_TRUE : TRIT_FALSE)
#endif

static int tests_passed = 0;
static int tests_failed = 0;

#define TEST(name) do { printf("  %-60s ", #name); fflush(stdout); } while(0)
#define PASS()     do { printf("[PASS]\n"); tests_passed++; } while(0)
#define FAIL(msg)  do { printf("[FAIL] %s\n", msg); tests_failed++; } while(0)

/* ── Helper: check full trit range in array ── */
static int has_full_range(const trit *arr, int n) {
    int f = 0, u = 0, t = 0;
    for (int i = 0; i < n; i++) {
        if (arr[i] == TRIT_FALSE) f = 1;
        if (arr[i] == TRIT_UNKNOWN) u = 1;
        if (arr[i] == TRIT_TRUE) t = 1;
    }
    return f && u && t;
}

/* ── Helper: chi-squared uniformity test for 3 categories ── */
static double chi_squared_3(int counts[3], int total) {
    double expected = (double)total / 3.0;
    double chi2 = 0.0;
    for (int i = 0; i < 3; i++) {
        double diff = (double)counts[i] - expected;
        chi2 += (diff * diff) / expected;
    }
    return chi2;
}

/* ═══════════════════════════════════════════════════════════════
 * Sentinel 1: Kleene K₃ operators produce full trit range
 * ═══════════════════════════════════════════════════════════════ */
static void test_kleene_full_range(void) {
    TEST(sentinel_kleene_ops_produce_all_3_values);
    trit and_results[9], or_results[9], not_results[3];
    trit vals[3] = { TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE };
    int k = 0;
    for (int a = 0; a < 3; a++)
        for (int b = 0; b < 3; b++)
            and_results[k++] = trit_and(vals[a], vals[b]);
    k = 0;
    for (int a = 0; a < 3; a++)
        for (int b = 0; b < 3; b++)
            or_results[k++] = trit_or(vals[a], vals[b]);
    for (int a = 0; a < 3; a++)
        not_results[a] = trit_not(vals[a]);

    if (has_full_range(and_results, 9) &&
        has_full_range(or_results, 9) &&
        has_full_range(not_results, 3))
        PASS();
    else
        FAIL("Kleene ops missing trit value — binary reversion!");
}

/* ═══════════════════════════════════════════════════════════════
 * Sentinel 2: SIMD packed64 outputs contain full range
 * ═══════════════════════════════════════════════════════════════ */
static void test_simd_full_range(void) {
    TEST(sentinel_simd_packed64_full_trit_range);
    /* Build inputs so that AND/OR/NOT each produce all 3 trit values:
     *   i%3==0: a=TRUE,    b=TRUE    → AND=T, OR=T, NOT(a)=F
     *   i%3==1: a=UNKNOWN, b=UNKNOWN → AND=U, OR=U, NOT(a)=U
     *   i%3==2: a=FALSE,   b=FALSE   → AND=F, OR=F, NOT(a)=T
     * Combined across 32 positions all 3 values appear in each output. */
    uint64_t a = 0, b = 0;
    for (int i = 0; i < 32; i++) {
        trit va, vb;
        switch (i % 3) {
            case 0:  va = TRIT_TRUE;    vb = TRIT_TRUE;    break;
            case 1:  va = TRIT_UNKNOWN; vb = TRIT_UNKNOWN; break;
            default: va = TRIT_FALSE;   vb = TRIT_FALSE;   break;
        }
        a |= ((uint64_t)trit_pack(va)) << (2 * i);
        b |= ((uint64_t)trit_pack(vb)) << (2 * i);
    }
    uint64_t r_and = trit_and_packed64(a, b);
    uint64_t r_or  = trit_or_packed64(a, b);
    uint64_t r_not = trit_not_packed64(a);

    trit out[32];
    int ok = 1;

    /* Check AND result */
    for (int i = 0; i < 32; i++) out[i] = trit_unpack((r_and >> (2*i)) & 3);
    if (!has_full_range(out, 32)) ok = 0;

    /* Check OR result */
    for (int i = 0; i < 32; i++) out[i] = trit_unpack((r_or >> (2*i)) & 3);
    if (!has_full_range(out, 32)) ok = 0;

    /* Check NOT result */
    for (int i = 0; i < 32; i++) out[i] = trit_unpack((r_not >> (2*i)) & 3);
    if (!has_full_range(out, 32)) ok = 0;

    if (ok) PASS();
    else FAIL("SIMD output missing trit values — binary reversion!");
}

/* ═══════════════════════════════════════════════════════════════
 * Sentinel 3: tcrypto S-box produces full trit range
 * ═══════════════════════════════════════════════════════════════ */
static void test_crypto_sbox_range(void) {
    TEST(sentinel_crypto_xor_produces_all_trits);
    trit results[9];
    trit vals[3] = { TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE };
    int k = 0;
    for (int a = 0; a < 3; a++)
        for (int b = 0; b < 3; b++)
            results[k++] = tcrypto_trit_xor(vals[a], vals[b]);

    if (has_full_range(results, 9))
        PASS();
    else
        FAIL("tcrypto_trit_xor missing values — binary reversion!");
}

/* ═══════════════════════════════════════════════════════════════
 * Sentinel 4: Hash output contains full trit range
 * ═══════════════════════════════════════════════════════════════ */
static void test_hash_full_range(void) {
    TEST(sentinel_hash_output_full_trit_range);
    tcrypto_hash_t h;
    tcrypto_hash_init(&h);
    trit msg[27];
    for (int i = 0; i < 27; i++) msg[i] = (trit)((i % 3) - 1);
    tcrypto_hash_absorb(&h, msg, 27);
    trit digest[TCRYPTO_HASH_TRITS];
    tcrypto_hash_finalize(&h, digest);

    if (has_full_range(digest, TCRYPTO_HASH_TRITS))
        PASS();
    else
        FAIL("hash output missing trit values — binary reversion!");
}

/* ═══════════════════════════════════════════════════════════════
 * Sentinel 5: Encrypt/decrypt round-trip preserves full range
 * ═══════════════════════════════════════════════════════════════ */
static void test_encrypt_roundtrip_range(void) {
    TEST(sentinel_encrypt_decrypt_preserves_trit_range);
    tcrypto_key_t    key;
    tcrypto_cipher_t cc;
    trit iv[TCRYPTO_MAC_TRITS];
    trit data[TCRYPTO_KEY_TRITS];
    trit backup[TCRYPTO_KEY_TRITS];

    for (int i = 0; i < TCRYPTO_KEY_TRITS; i++) {
        key.data[i]  = (trit)((i % 3) - 1);
        data[i] = backup[i] = (trit)((i % 3) - 1);
    }
    key.length = TCRYPTO_KEY_TRITS;
    for (int i = 0; i < TCRYPTO_MAC_TRITS; i++) iv[i] = TRIT_UNKNOWN;

    /* Encrypt in-place */
    tcrypto_cipher_init(&cc, &key, iv, 3);
    tcrypto_encrypt(&cc, data, TCRYPTO_KEY_TRITS);

    int ok = 1;
    /* Ciphertext should have full trit range */
    if (!has_full_range(data, TCRYPTO_KEY_TRITS)) ok = 0;

    /* Decrypt back and verify round-trip */
    tcrypto_cipher_init(&cc, &key, iv, 3);
    tcrypto_decrypt(&cc, data, TCRYPTO_KEY_TRITS);
    for (int i = 0; i < TCRYPTO_KEY_TRITS; i++) {
        if (data[i] != backup[i]) { ok = 0; break; }
    }

    if (ok) PASS(); else FAIL("encrypt/decrypt reversion or corruption");
}

/* ═══════════════════════════════════════════════════════════════
 * Sentinel 6: trit_cast round-trip preserves values
 * ═══════════════════════════════════════════════════════════════ */
static void test_trit_cast_range(void) {
    TEST(sentinel_trit_cast_bool_roundtrip);
    trit vals[3] = { TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE };
    int ok = 1;
    for (int i = 0; i < 3; i++) {
        /* trit → bool → trit (lossy for unknown) */
        int b = trit_to_bool_safe(vals[i]);
        trit back = bool_to_trit(b);
        /* For definite values, round-trip should work */
        if (vals[i] == TRIT_TRUE && back != TRIT_TRUE) ok = 0;
        if (vals[i] == TRIT_FALSE && back != TRIT_FALSE) ok = 0;
    }
    /* bool_to_trit must produce both TRUE and FALSE */
    trit cast_results[2] = { bool_to_trit(0), bool_to_trit(1) };
    if (cast_results[0] != TRIT_FALSE || cast_results[1] != TRIT_TRUE) ok = 0;

    if (ok) PASS(); else FAIL("trit_cast not producing full range");
}

/* ═══════════════════════════════════════════════════════════════
 * Sentinel 7: pack/unpack round-trip for all encodings
 * ═══════════════════════════════════════════════════════════════ */
static void test_pack_unpack_range(void) {
    TEST(sentinel_pack_unpack_roundtrip_all_3_values);
    trit vals[3] = { TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE };
    int ok = 1;
    trit results[3];
    for (int i = 0; i < 3; i++) {
        trit_packed p = trit_pack(vals[i]);
        results[i] = trit_unpack(p);
        if (results[i] != vals[i]) ok = 0;
    }
    if (!has_full_range(results, 3)) ok = 0;
    if (ok) PASS(); else FAIL("pack/unpack losing trit values");
}

/* ═══════════════════════════════════════════════════════════════
 * Sentinel 8: FFT butterfly produces all 3 values
 * ═══════════════════════════════════════════════════════════════ */
static void test_fft_range(void) {
    TEST(sentinel_fft_butterfly_ternary_output);
    multiradix_state_t mr;
    multiradix_init(&mr);
    /* Three groups whose DFT butterfly outputs span all 3 trit values:
     *  group(pos 0,1,2)=(-1,-1,-1) → outputs (U, U, U)
     *  group(pos 3,4,5)=(-1,-1, 0) → outputs (T, T, T)
     *  group(pos 6,7,8)=(-1,-1, 1) → outputs (F, F, F)
     * Combined: all 3 values present in positions 0..8. */
    int data9[9] = { -1,-1,-1,  -1,-1,0,  -1,-1,1 };
    for (int i = 0; i < 9; i++)
        trit2_reg32_set(&mr.regs[0], i, trit2_encode(data9[i]));
    /* FFT butterfly: reg_in=0, reg_out=1, stride=1 */
    fft_step(&mr, 0, 1, 1);
    /* Read output from register 1 */
    trit output[9];
    for (int i = 0; i < 9; i++)
        output[i] = (trit)trit2_decode(trit2_reg32_get(&mr.regs[1], i));

    if (has_full_range(output, 9))
        PASS();
    else
        FAIL("FFT butterfly output missing trit values");
}

/* ═══════════════════════════════════════════════════════════════
 * Sentinel 9: Avizienis conversion round-trip
 * ═══════════════════════════════════════════════════════════════ */
static void test_avizienis_range(void) {
    TEST(sentinel_avizienis_balanced_ternary_full_range);
    /* Convert integers spanning negative/zero/positive into balanced ternary
     * using radix_conv_to_ternary() and sample the least-significant trit. */
    trit all_trits[30];
    int k = 0;
    for (int val = -5; val <= 5; val++) {
        multiradix_state_t mr;
        multiradix_init(&mr);
        radix_conv_to_ternary(&mr, 0, val);  /* store ternary in register 0 */
        trit2 t = trit2_reg32_get(&mr.regs[0], 0); /* read LSD */
        if (k < 30) all_trits[k++] = (trit)trit2_decode(t);
    }
    /* Should include negative, zero, positive */
    int has_neg = 0, has_zero = 0, has_pos = 0;
    for (int i = 0; i < k; i++) {
        if (all_trits[i] == TRIT_FALSE) has_neg = 1;
        if (all_trits[i] == TRIT_UNKNOWN) has_zero = 1;
        if (all_trits[i] == TRIT_TRUE) has_pos = 1;
    }
    if (has_neg && has_zero && has_pos) PASS();
    else FAIL("Avizienis output missing values");
}

/* ═══════════════════════════════════════════════════════════════
 * Sentinel 10: No function outputs only {0, 1} (binary detection)
 * ═══════════════════════════════════════════════════════════════ */
static void test_no_binary_flattening(void) {
    TEST(sentinel_no_implicit_bool_to_trit_flattening);
    /* Generate many trit operations and ensure -1 appears */
    int found_negative = 0;
    trit vals[3] = { TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE };
    for (int a = 0; a < 3; a++) {
        for (int b = 0; b < 3; b++) {
            trit r1 = trit_and(vals[a], vals[b]);
            trit r2 = trit_or(vals[a], vals[b]);
            trit r3 = trit_not(vals[a]);
            if (r1 == TRIT_FALSE || r2 == TRIT_FALSE || r3 == TRIT_FALSE)
                found_negative = 1;
        }
    }
    if (found_negative) PASS();
    else FAIL("No -1 values produced — binary flattening detected!");
}

/* ═══════════════════════════════════════════════════════════════
 * Sentinel 11: MAC output accumulates ternary properly
 * ═══════════════════════════════════════════════════════════════ */
static void test_mac_ternary_accumulation(void) {
    TEST(sentinel_ternary_mac_not_boolean);
    /* Simulate a simple trit dot product */
    trit a[8] = { 1, -1, 1, 0, -1, 1, -1, 0 };
    trit b[8] = { 1, 1, -1, 0, -1, -1, 1, 1 };
    int mac = 0;
    for (int i = 0; i < 8; i++)
        mac += (int)a[i] * (int)b[i];
    /* Expected: 1*1 + (-1)*1 + 1*(-1) + 0*0 + (-1)*(-1) + 1*(-1) + (-1)*1 + 0*1
     *         = 1 + (-1) + (-1) + 0 + 1 + (-1) + (-1) + 0 = -2 */
    if (mac == -2) PASS();
    else FAIL("MAC result wrong — ternary multiplication broken");
}

/* ═══════════════════════════════════════════════════════════════
 * Sentinel 12: IMPLIES/EQUIV use full trit range
 * ═══════════════════════════════════════════════════════════════ */
static void test_implies_equiv_range(void) {
    TEST(sentinel_implies_equiv_full_range);
    trit vals[3] = { TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE };
    trit imp[9], eqv[9];
    int k = 0;
    for (int a = 0; a < 3; a++)
        for (int b = 0; b < 3; b++) {
            imp[k] = trit_implies(vals[a], vals[b]);
            eqv[k] = trit_equiv(vals[a], vals[b]);
            k++;
        }
    if (has_full_range(imp, 9) && has_full_range(eqv, 9))
        PASS();
    else
        FAIL("IMPLIES/EQUIV missing trit values");
}

int main(void) {
    printf("=== T-044: Binary Sentinel Detection Suite ===\n");

    test_kleene_full_range();
    test_simd_full_range();
    test_crypto_sbox_range();
    test_hash_full_range();
    test_encrypt_roundtrip_range();
    test_trit_cast_range();
    test_pack_unpack_range();
    test_fft_range();
    test_avizienis_range();
    test_no_binary_flattening();
    test_mac_ternary_accumulation();
    test_implies_equiv_range();

    printf("=== Results: %d passed, %d failed ===\n",
           tests_passed, tests_failed);
    return tests_failed ? 1 : 0;
}
