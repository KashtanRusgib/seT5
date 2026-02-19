/**
 * @file trit_rns.c
 * @brief seT6 Residue Number System — Output-Parameter API Implementation
 *
 * Implements all functions declared in include/set5/trit_rns.h.
 * Moduli {3, 5, 7}, CRT reconstruction, carry-free arithmetic,
 * Montgomery REDC, mixed-radix conversion, and PVT noise injection.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/trit_rns.h"
#include <string.h>
#include <stdlib.h>

/* ==== Internal helpers ================================================= */

/** Positive modulo: always returns [0, m). */
static int posmod(int a, int m) {
    int r = a % m;
    return r < 0 ? r + m : r;
}

/** Extended GCD: returns gcd, sets *x, *y for ax + by = gcd. */
static int extgcd(int a, int b, int *x, int *y) {
    if (b == 0) { *x = 1; *y = 0; return a; }
    int x1, y1;
    int g = extgcd(b, a % b, &x1, &y1);
    *x = y1;
    *y = x1 - (a / b) * y1;
    return g;
}

/** Modular inverse: a^(-1) mod m.  Returns 0 if gcd != 1. */
static int modinv(int a, int m) {
    int x, y;
    int g = extgcd(posmod(a, m), m, &x, &y);
    (void)y;
    if (g != 1) return 0;
    return posmod(x, m);
}

/** GCD for coprimality checks */
uint32_t rns_gcd_public(uint32_t a, uint32_t b) {
    while (b) { uint32_t t = b; b = a % b; a = t; }
    return a;
}

/* ==== API Implementation =============================================== */

int trit_rns_init(trit_rns_context_t *ctx) {
    if (!ctx) return -1;
    memset(ctx, 0, sizeof(*ctx));
    ctx->count = RNS_MODULI_COUNT;
    for (uint32_t i = 0; i < RNS_MODULI_COUNT; i++)
        ctx->moduli[i] = rns_initial_moduli[i];
    ctx->M = 1;
    for (uint32_t i = 0; i < ctx->count; i++)
        ctx->M *= ctx->moduli[i];
    for (uint32_t i = 0; i < ctx->count; i++) {
        ctx->Mi[i] = ctx->M / ctx->moduli[i];
        ctx->Mi_inv[i] = (uint32_t)modinv((int)ctx->Mi[i], (int)ctx->moduli[i]);
    }
    return 0;
}

int trit_rns_init_custom(trit_rns_context_t *ctx,
                         const uint32_t *moduli, uint32_t count) {
    if (!ctx || !moduli || count == 0 || count > RNS_MAX_MODULI) return -1;
    for (uint32_t i = 0; i < count; i++)
        if (moduli[i] <= 1) return -1;
    for (uint32_t i = 0; i < count; i++)
        for (uint32_t j = i + 1; j < count; j++)
            if (rns_gcd_public(moduli[i], moduli[j]) != 1) return -1;
    memset(ctx, 0, sizeof(*ctx));
    ctx->count = count;
    for (uint32_t i = 0; i < count; i++)
        ctx->moduli[i] = moduli[i];
    ctx->M = 1;
    for (uint32_t i = 0; i < count; i++)
        ctx->M *= ctx->moduli[i];
    for (uint32_t i = 0; i < count; i++) {
        ctx->Mi[i] = ctx->M / ctx->moduli[i];
        ctx->Mi_inv[i] = (uint32_t)modinv((int)ctx->Mi[i], (int)ctx->moduli[i]);
    }
    return 0;
}

/** Decode a trit2 value to balanced integer {-1, 0, +1}. */
static int trit2_to_int(trit2 t) {
    switch (t) {
        case TRIT2_FALSE:   return -1;
        case TRIT2_UNKNOWN: return  0;
        case TRIT2_TRUE:    return  1;
        default:            return  0;
    }
}

/** Encode a balanced integer {-1,0,+1} as trit2. */
static trit2 int_to_trit2(int v) {
    if (v < 0) return TRIT2_FALSE;
    if (v > 0) return TRIT2_TRUE;
    return TRIT2_UNKNOWN;
}

void trit_to_rns(const trit2_reg32 *trit_vec, int n_trits,
                  trit_rns_t *rns_out, const trit_rns_context_t *ctx) {
    if (!trit_vec || !rns_out || !ctx || n_trits < 1) { if (rns_out) memset(rns_out, 0, sizeof(*rns_out)); return; }
    if (n_trits > 32) n_trits = 32;
    for (uint32_t ch = 0; ch < ctx->count; ch++) {
        int m = (int)ctx->moduli[ch];
        int acc = 0;
        for (int i = n_trits - 1; i >= 0; i--) {
            int digit = trit2_to_int(trit2_reg32_get(trit_vec, i));
            acc = posmod(acc * 3 + digit, m);
        }
        rns_out->residues[ch] = (uint32_t)acc;
    }
}

void rns_to_trit(const trit_rns_t *rns_in, int n_trits,
                  trit2_reg32 *trit_out, const trit_rns_context_t *ctx) {
    if (!rns_in || !trit_out || !ctx || n_trits < 1) {
        if (trit_out) trit_out->bits = 0x5555555555555555ULL;
        return;
    }
    if (n_trits > 32) n_trits = 32;
    int64_t val = 0;
    for (uint32_t i = 0; i < ctx->count; i++) {
        val += (int64_t)rns_in->residues[i] * (int64_t)ctx->Mi[i] *
               (int64_t)ctx->Mi_inv[i];
    }
    int x = (int)(val % (int64_t)ctx->M);
    if (x < 0) x += (int)ctx->M;
    if (x > (int)(ctx->M / 2)) x -= (int)ctx->M;
    /* Convert signed integer to balanced ternary digits */
    trit_out->bits = 0;
    int rem_val = x;
    for (int i = 0; i < n_trits; i++) {
        int digit = 0;
        if (rem_val != 0) {
            int r = posmod(rem_val, 3);
            if (r == 0) { digit = 0; }
            else if (r == 1) { digit = 1; rem_val -= 1; }
            else /* r==2 */ { digit = -1; rem_val += 1; }
            rem_val /= 3;
        }
        trit2_reg32_set(trit_out, i, int_to_trit2(digit));
    }
}

void rns_add(const trit_rns_t *a, const trit_rns_t *b,
              trit_rns_t *out, const trit_rns_context_t *ctx) {
    if (!a || !b || !out || !ctx) { if (out) memset(out, 0, sizeof(*out)); return; }
    for (uint32_t i = 0; i < ctx->count; i++)
        out->residues[i] = (a->residues[i] + b->residues[i]) % ctx->moduli[i];
}

void rns_sub(const trit_rns_t *a, const trit_rns_t *b,
              trit_rns_t *out, const trit_rns_context_t *ctx) {
    if (!a || !b || !out || !ctx) return;
    for (uint32_t i = 0; i < ctx->count; i++)
        out->residues[i] = (uint32_t)posmod((int)a->residues[i] - (int)b->residues[i],
                                              (int)ctx->moduli[i]);
}

void rns_mul(const trit_rns_t *a, const trit_rns_t *b,
              trit_rns_t *out, const trit_rns_context_t *ctx) {
    if (!a || !b || !out || !ctx) return;
    for (uint32_t i = 0; i < ctx->count; i++)
        out->residues[i] = (a->residues[i] * b->residues[i]) % ctx->moduli[i];
}

void rns_montgomery_mul(const trit_rns_t *a, const trit_rns_t *b,
                          trit_rns_t *out, const trit_rns_context_t *ctx) {
    if (!a || !b || !out || !ctx) { if (out) memset(out, 0, sizeof(*out)); return; }
    for (uint32_t i = 0; i < ctx->count; i++) {
        uint32_t m = ctx->moduli[i];
        uint32_t R = 3;
        while (R <= m) R *= 3;
        int n_prime = posmod(-(int)modinv((int)m, (int)R), (int)R);
        uint32_t t = a->residues[i] * b->residues[i];
        uint32_t u = (t * (uint32_t)n_prime) % R;
        uint64_t v = (uint64_t)t + (uint64_t)u * m;
        out->residues[i] = (uint32_t)((v / R) % m);
    }
}

bool rns_is_zero(const trit_rns_t *rns, const trit_rns_context_t *ctx) {
    if (!rns || !ctx) return false;
    for (uint32_t i = 0; i < ctx->count; i++)
        if (rns->residues[i] != 0) return false;
    return true;
}

int rns_validate(const trit_rns_t *rns, const trit_rns_context_t *ctx) {
    if (!rns || !ctx) return -1;
    for (uint32_t i = 0; i < ctx->count; i++)
        if (rns->residues[i] >= ctx->moduli[i]) return -1;
    return 0;
}

int rns_extend_moduli(trit_rns_context_t *ctx, uint32_t new_modulus) {
    if (!ctx || ctx->count >= RNS_MAX_MODULI || new_modulus <= 1) return -1;
    for (uint32_t i = 0; i < ctx->count; i++)
        if (rns_gcd_public(ctx->moduli[i], new_modulus) != 1) return -1;
    ctx->moduli[ctx->count] = new_modulus;
    ctx->count++;
    ctx->M = 1;
    for (uint32_t i = 0; i < ctx->count; i++)
        ctx->M *= ctx->moduli[i];
    for (uint32_t i = 0; i < ctx->count; i++) {
        ctx->Mi[i] = ctx->M / ctx->moduli[i];
        ctx->Mi_inv[i] = (uint32_t)modinv((int)ctx->Mi[i], (int)ctx->moduli[i]);
    }
    return 0;
}

void rns_apply_noise(trit_rns_t *rns, double noise_prob,
                       const trit_rns_context_t *ctx) {
    if (!rns || !ctx) return;
    for (uint32_t i = 0; i < ctx->count; i++) {
        double roll = (double)rand() / (double)RAND_MAX;
        if (roll < noise_prob)
            rns->residues[i] = (uint32_t)(rand() % (int)ctx->moduli[i]);
    }
}

int rns_to_mrs(const trit_rns_t *rns, uint32_t *digits,
               const trit_rns_context_t *ctx) {
    if (!rns || !digits || !ctx) return -1;
    uint32_t v[RNS_MAX_MODULI];
    for (uint32_t i = 0; i < ctx->count; i++)
        v[i] = rns->residues[i];
    for (uint32_t i = 0; i < ctx->count; i++) {
        digits[i] = v[i] % ctx->moduli[i];
        for (uint32_t j = i + 1; j < ctx->count; j++) {
            int inv = modinv((int)ctx->moduli[i], (int)ctx->moduli[j]);
            v[j] = (uint32_t)posmod((int)(v[j] - digits[i]) * inv,
                                     (int)ctx->moduli[j]);
        }
    }
    return 0;
}

int rns_from_mrs(const uint32_t *digits, trit_rns_t *rns_out,
                 const trit_rns_context_t *ctx) {
    if (!digits || !rns_out || !ctx) return -1;
    int64_t val = 0;
    int64_t weight = 1;
    for (uint32_t i = 0; i < ctx->count; i++) {
        val += (int64_t)digits[i] * weight;
        weight *= (int64_t)ctx->moduli[i];
    }
    int x = (int)(val % (int64_t)ctx->M);
    if (x < 0) x += (int)ctx->M;
    for (uint32_t i = 0; i < ctx->count; i++)
        rns_out->residues[i] = (uint32_t)posmod(x, (int)ctx->moduli[i]);
    return 0;
}

int rns_montgomery_exp(const trit_rns_t *base, uint32_t exp,
                       trit_rns_t *out, const trit_rns_context_t *ctx) {
    if (!base || !out || !ctx) return -1;
    trit_rns_t result, b;
    for (uint32_t i = 0; i < ctx->count; i++) {
        result.residues[i] = 1 % ctx->moduli[i];
        b.residues[i] = base->residues[i];
    }
    while (exp > 0) {
        if (exp & 1) rns_mul(&result, &b, &result, ctx);
        rns_mul(&b, &b, &b, ctx);
        exp >>= 1;
    }
    *out = result;
    return 0;
}

int rns_add_redundant_check(trit_rns_context_t *ctx) {
    if (!ctx || ctx->count >= RNS_MAX_MODULI) return -1;
    uint32_t candidate = ctx->moduli[ctx->count - 1] + 2;
    for (;;) {
        int coprime = 1;
        for (uint32_t i = 0; i < ctx->count; i++)
            if (rns_gcd_public(ctx->moduli[i], candidate) != 1) { coprime = 0; break; }
        if (coprime) {
            int prime = 1;
            for (uint32_t d = 2; d * d <= candidate; d++)
                if (candidate % d == 0) { prime = 0; break; }
            if (prime) return rns_extend_moduli(ctx, candidate);
        }
        candidate++;
    }
}

int rns_detect_correct(const trit_rns_t *rns, trit_rns_t *corrected,
                       const trit_rns_context_t *ctx) {
    if (!rns || !corrected || !ctx) return -1;
    /* Need at least 2 moduli for error detection */
    if (ctx->count < 2) return -1;
    *corrected = *rns;
    if (rns_validate(rns, ctx) != 0) return -1;
    return 0;
}
