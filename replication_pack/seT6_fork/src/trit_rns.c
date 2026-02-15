/**
 * @file trit_rns.c
 * @brief seT6 Residue Number System — Implementation
 *
 * RNS with moduli {3, 5, 7}, CRT reconstruction, Montgomery modular
 * multiplication, mixed-radix conversion, and overflow detection.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "trit_rns.h"
#include <string.h>

/* ==== Internal helpers ================================================= */

/** Positive modulo: always returns [0, m). */
static int posmod(int a, int m) {
    int r = a % m;
    return r < 0 ? r + m : r;
}

/** Extended GCD: returns gcd, sets *x, *y for ax + by = gcd */
static int extgcd(int a, int b, int *x, int *y) {
    if (b == 0) { *x = 1; *y = 0; return a; }
    int x1, y1;
    int g = extgcd(b, a % b, &x1, &y1);
    *x = y1;
    *y = x1 - (a / b) * y1;
    return g;
}

/** Modular inverse: a^(-1) mod m.  Returns -1 if non-invertible. */
static int modinv(int a, int m) {
    int x, y;
    int g = extgcd(posmod(a, m), m, &x, &y);
    if (g != 1) return -1;
    return posmod(x, m);
}

/* ==== Public API ======================================================= */

static const int MODULI[RNS_NUM_MODULI] = { RNS_M0, RNS_M1, RNS_M2 };

int rns_init(rns_state_t *st) {
    if (!st) return -1;
    memset(st, 0, sizeof(*st));

    /* Precompute CRT constants */
    st->crt.M = RNS_DYNAMIC_RANGE; /* 3 × 5 × 7 = 105 */

    for (int i = 0; i < RNS_NUM_MODULI; i++) {
        st->crt.Mi[i] = st->crt.M / MODULI[i];
        st->crt.yi[i] = modinv(st->crt.Mi[i], MODULI[i]);
    }
    /* Verify: Mi[0]=35, yi[0]=35^(-1) mod 3 = 2^(-1) mod 3 = 2
     *         Mi[1]=21, yi[1]=21^(-1) mod 5 = 1^(-1) mod 5 = 1
     *         Mi[2]=15, yi[2]=15^(-1) mod 7 = 1^(-1) mod 7 = 1 */

    st->initialized = 1;
    return 0;
}

rns_residue_t rns_forward(const rns_state_t *st, int value) {
    rns_residue_t res = {{0, 0, 0}};
    if (!st || !st->initialized) return res;
    for (int i = 0; i < RNS_NUM_MODULI; i++) {
        res.r[i] = posmod(value, MODULI[i]);
    }
    return res;
}

int rns_inverse(const rns_state_t *st, rns_residue_t res) {
    if (!st || !st->initialized) return 0;

    /* CRT: x = Σ (ri × Mi × yi) mod M */
    int64_t x = 0;
    for (int i = 0; i < RNS_NUM_MODULI; i++) {
        x += (int64_t)res.r[i] * st->crt.Mi[i] * st->crt.yi[i];
    }
    int result = (int)(x % st->crt.M);
    if (result < 0) result += st->crt.M;

    /* Signed representation: [-52, 52] */
    if (result > RNS_HALF_RANGE) {
        result -= st->crt.M;
    }
    return result;
}

rns_residue_t rns_add(const rns_state_t *st, rns_residue_t a, rns_residue_t b) {
    rns_residue_t res = {{0, 0, 0}};
    if (!st || !st->initialized) return res;
    for (int i = 0; i < RNS_NUM_MODULI; i++) {
        res.r[i] = posmod(a.r[i] + b.r[i], MODULI[i]);
    }
    return res;
}

rns_residue_t rns_sub(const rns_state_t *st, rns_residue_t a, rns_residue_t b) {
    rns_residue_t res = {{0, 0, 0}};
    if (!st || !st->initialized) return res;
    for (int i = 0; i < RNS_NUM_MODULI; i++) {
        res.r[i] = posmod(a.r[i] - b.r[i], MODULI[i]);
    }
    return res;
}

rns_residue_t rns_mul(const rns_state_t *st, rns_residue_t a, rns_residue_t b) {
    rns_residue_t res = {{0, 0, 0}};
    if (!st || !st->initialized) return res;
    for (int i = 0; i < RNS_NUM_MODULI; i++) {
        res.r[i] = posmod(a.r[i] * b.r[i], MODULI[i]);
    }
    return res;
}

rns_residue_t rns_negate(const rns_state_t *st, rns_residue_t a) {
    rns_residue_t res = {{0, 0, 0}};
    if (!st || !st->initialized) return res;
    for (int i = 0; i < RNS_NUM_MODULI; i++) {
        res.r[i] = posmod(-a.r[i], MODULI[i]);
    }
    return res;
}

int rns_is_zero(rns_residue_t a) {
    for (int i = 0; i < RNS_NUM_MODULI; i++) {
        if (a.r[i] != 0) return 0;
    }
    return 1;
}

int rns_compare(const rns_state_t *st, rns_residue_t a, rns_residue_t b) {
    if (!st) return 0;
    int va = rns_inverse(st, a);
    int vb = rns_inverse(st, b);
    if (va < vb) return -1;
    if (va > vb) return 1;
    return 0;
}

int rns_mrc_inverse(const rns_state_t *st, rns_residue_t res) {
    if (!st || !st->initialized) return 0;

    /* Mixed-Radix Conversion (Garner's algorithm):
     * v0 = r0
     * v1 = (r1 - v0) × m0^(-1) mod m1
     * v2 = ((r2 - v0) × m0^(-1) - v1) × m1^(-1) mod m2
     * x = v0 + v1×m0 + v2×m0×m1
     */
    int m0_inv_m1 = modinv(MODULI[0], MODULI[1]); /* 3^(-1) mod 5 = 2 */
    int m0_inv_m2 = modinv(MODULI[0], MODULI[2]); /* 3^(-1) mod 7 = 5 */
    int m1_inv_m2 = modinv(MODULI[1], MODULI[2]); /* 5^(-1) mod 7 = 3 */

    int v0 = res.r[0];
    int v1 = posmod((res.r[1] - v0) * m0_inv_m1, MODULI[1]);
    int v2 = posmod(posmod((res.r[2] - v0) * m0_inv_m2, MODULI[2]) - v1, MODULI[2]);
    v2 = posmod(v2 * m1_inv_m2, MODULI[2]);

    int result = v0 + v1 * MODULI[0] + v2 * MODULI[0] * MODULI[1];

    /* Signed representation */
    if (result > RNS_HALF_RANGE) {
        result -= st->crt.M;
    }
    return result;
}

int rns_detect_overflow(const rns_state_t *st, rns_residue_t a, rns_residue_t b) {
    if (!st) return -1;
    int va = rns_inverse(st, a);
    int vb = rns_inverse(st, b);

    /* Check if a+b would overflow the dynamic range */
    int64_t sum = (int64_t)va + vb;
    if (sum > RNS_HALF_RANGE || sum < -RNS_HALF_RANGE) return 1;

    /* Check if a*b would overflow */
    int64_t prod = (int64_t)va * vb;
    if (prod > RNS_HALF_RANGE || prod < -RNS_HALF_RANGE) return 1;

    return 0;
}

/* ==== Montgomery Modular Multiplication ================================ */

int rns_montgomery_init(rns_montgomery_t *mont, int modulus) {
    if (!mont || modulus <= 1) return -1;
    memset(mont, 0, sizeof(*mont));

    mont->modulus = modulus;

    /* Choose R as smallest power of 3 > N (ternary-aligned!) */
    mont->R = 3;
    while (mont->R <= modulus) mont->R *= 3;

    /* R^(-1) mod N */
    mont->R_inv_mod_N = modinv(mont->R, modulus);
    if (mont->R_inv_mod_N < 0) return -1;

    /* -N^(-1) mod R (N_prime) */
    int n_inv = modinv(modulus, mont->R);
    if (n_inv < 0) return -1;
    mont->N_prime = posmod(-n_inv, mont->R);

    /* R^2 mod N */
    int64_t r2 = ((int64_t)mont->R * mont->R) % modulus;
    mont->R2_mod_N = (int)r2;

    return 0;
}

int rns_montgomery_mul(rns_montgomery_t *mont, int a_mont, int b_mont) {
    if (!mont || mont->modulus <= 1) return 0;

    /* REDC: t = a*b, u = (t * N') mod R, result = (t + u*N) / R */
    int64_t t = (int64_t)a_mont * b_mont;
    int64_t u = (t * mont->N_prime) % mont->R;
    if (u < 0) u += mont->R;
    int64_t result = (t + u * mont->modulus) / mont->R;

    if (result >= mont->modulus) result -= mont->modulus;
    if (result < 0) result += mont->modulus;

    mont->ops_count++;
    return (int)result;
}

int rns_to_montgomery(const rns_montgomery_t *mont, int a) {
    if (!mont) return 0;
    /* aR = a × R^2 × R^(-1) mod N — but simpler: (a * R) mod N */
    int64_t result = ((int64_t)posmod(a, mont->modulus) * mont->R) % mont->modulus;
    return (int)result;
}

int rns_from_montgomery(const rns_montgomery_t *mont, int a_mont) {
    if (!mont) return 0;
    /* a = aR × R^(-1) mod N */
    int64_t result = ((int64_t)posmod(a_mont, mont->modulus) * mont->R_inv_mod_N) % mont->modulus;
    return (int)result;
}

rns_residue_t rns_from_trits(const rns_state_t *st, const trit *trits, int len) {
    rns_residue_t res = {{0, 0, 0}};
    if (!st || !st->initialized || !trits || len <= 0) return res;

    /* Interpret trit array as balanced ternary: value = Σ t_i × 3^i */
    int value = 0;
    int power = 1;
    for (int i = 0; i < len && i < 4; i++) { /* max 4 trits for range */
        value += trits[i] * power;
        power *= 3;
    }

    return rns_forward(st, value);
}

int rns_get_ternary_ratio(const rns_state_t *st) {
    if (!st || st->total_ops == 0) return 0;
    return (st->ternary_direct * 100) / st->total_ops;
}

int rns_get_binary_fallbacks(const rns_state_t *st) {
    if (!st) return 0;
    return st->binary_fallbacks;
}
