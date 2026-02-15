/**
 * @file multiradix.c
 * @brief seT6 Multi-Radix Instructions — Implementation
 *
 * Implements DOT_TRIT, FFT_STEP, RADIX_CONV, and TRIT_LB instructions
 * for the seT6 balanced ternary microkernel.
 *
 * Key design choices:
 *   - DOT_TRIT uses element-wise ternary multiplication (balanced product)
 *     and skip-zero sparsity for N:M structured patterns (TENET-style).
 *   - FFT_STEP implements a radix-3 butterfly using the cyclic group Z/3Z
 *     which maps naturally to balanced ternary rotation (-1 → 0 → +1 → -1).
 *   - RADIX_CONV uses Avizienis signed-digit decomposition for balanced
 *     ternary — the standard algorithm from 1961.
 *   - TRIT_LB provides G300-inspired telemetry for adaptive scheduling.
 *
 * Hardware alignment:
 *   - Carry-lookahead accumulation (Huawei CN119652311A) for DOT_TRIT
 *   - CMOS-ternary mapping (Samsung) for the butterfly rotation
 *   - Memristive spill (1T1M) for register file overflow
 *   - Synthesizable to iCE40/Artix-7 FPGA via ternary_alu.v
 *
 * @see include/set6/multiradix.h for full API documentation
 * @see ARCHITECTURE.md §6 for hardware alignment details
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set6/multiradix.h"
#include "set6/trit_cast.h"
#include <string.h>

/* ==== Helpers ========================================================== */

/**
 * @brief Ternary multiplication (balanced): product of two trits.
 *
 * Truth table:
 *   +1 * +1 = +1    +1 * 0 = 0     +1 * -1 = -1
 *    0 * x  = 0     -1 * -1 = +1   -1 * +1 = -1
 */
static inline int trit_mul(int a, int b) {
    return a * b;  /* balanced ternary: integer product is correct */
}

/**
 * @brief Balanced ternary addition modulo 3.
 *
 * Maps the sum into balanced range: -1, 0, +1.
 * Used by FFT butterfly for the ternary rotation group.
 */
static inline int trit_add_mod3(int a, int b) {
    int s = a + b;
    if (s > 1) return s - 3;
    if (s < -1) return s + 3;
    return s;
}

/**
 * @brief Cyclic rotation ω: -1 → 0 → +1 → -1 (twiddle factor).
 */
static inline int trit_rotate(int t) {
    if (t == -1) return 0;
    if (t == 0)  return 1;
    /* t == +1 */ return -1;
}

/**
 * @brief Double rotation ω²: -1 → +1 → 0 → -1.
 */
static inline int trit_rotate2(int t) {
    return trit_rotate(trit_rotate(t));
}

/* ==== Init ============================================================= */

void multiradix_init(multiradix_state_t *state) {
    if (!state) return;

    /* All registers → Unknown */
    for (int i = 0; i < MR_NUM_REGS; i++) {
        state->regs[i] = trit2_reg32_splat(TRIT2_UNKNOWN);
    }

    /* Accumulators */
    state->dot_acc         = 0;
    state->dot_sparse_skip = 0;
    state->dot_total_ops   = 0;
    state->fft_stage       = 0;

    /* Telemetry */
    state->lb_total_insns   = 0;
    state->lb_trit_insns    = 0;
    state->lb_sparse_hits   = 0;
    state->lb_thermal_limit = 0;
    state->lb_affinity_migr = 0;
}

/* ==== DOT_TRIT ========================================================= */

int dot_trit(multiradix_state_t *state, int reg_a, int reg_b) {
    if (!state) return 0;
    if (reg_a < 0 || reg_a >= MR_NUM_REGS) return 0;
    if (reg_b < 0 || reg_b >= MR_NUM_REGS) return 0;

    trit2_reg32 *a = &state->regs[reg_a];
    trit2_reg32 *b = &state->regs[reg_b];

    int sparse_a = trit2_reg32_is_sparse(*a);
    int sparse_b = trit2_reg32_is_sparse(*b);
    int use_sparse = sparse_a || sparse_b;

    int acc = 0;
    int skipped = 0;

    for (int i = 0; i < MR_REG_WIDTH; i++) {
        int va = trit2_decode(trit2_reg32_get(a, i));
        int vb = trit2_decode(trit2_reg32_get(b, i));

        /* Sparsity: skip if either operand is zero */
        if (use_sparse && (va == 0 || vb == 0)) {
            skipped++;
            continue;
        }

        acc += trit_mul(va, vb);
    }

    state->dot_acc          = acc;
    state->dot_sparse_skip += skipped;
    state->dot_total_ops   += MR_REG_WIDTH;

    /* Telemetry */
    state->lb_total_insns++;
    state->lb_trit_insns++;
    if (skipped > 0) state->lb_sparse_hits++;

    return acc;
}

int dot_trit_sparse(multiradix_state_t *state, int reg_a, int reg_b,
                    int n, int m) {
    if (!state) return 0;
    if (reg_a < 0 || reg_a >= MR_NUM_REGS) return 0;
    if (reg_b < 0 || reg_b >= MR_NUM_REGS) return 0;
    if (n <= 0 || m <= 0 || m > n) return 0;

    trit2_reg32 *a = &state->regs[reg_a];
    trit2_reg32 *b = &state->regs[reg_b];

    int acc = 0;
    int skipped = 0;

    for (int block = 0; block < MR_REG_WIDTH; block += n) {
        /* Count non-zero in this N-trit block of reg_a */
        int nonzero = 0;
        for (int j = 0; j < n && (block + j) < MR_REG_WIDTH; j++) {
            int va = trit2_decode(trit2_reg32_get(a, block + j));
            if (va != 0) nonzero++;
        }

        /* Process block with M-cap enforcement */
        int kept = 0;
        for (int j = 0; j < n && (block + j) < MR_REG_WIDTH; j++) {
            int idx = block + j;
            int va = trit2_decode(trit2_reg32_get(a, idx));
            int vb = trit2_decode(trit2_reg32_get(b, idx));

            if (va == 0 || vb == 0) {
                skipped++;
                continue;
            }

            if (kept >= m) {
                skipped++;
                continue;  /* Enforce N:M — drop excess non-zeros */
            }

            acc += trit_mul(va, vb);
            kept++;
        }
    }

    state->dot_acc          = acc;
    state->dot_sparse_skip += skipped;
    state->dot_total_ops   += MR_REG_WIDTH;

    state->lb_total_insns++;
    state->lb_trit_insns++;
    if (skipped > 0) state->lb_sparse_hits++;

    return acc;
}

/* ==== FFT_STEP ========================================================= */

int fft_step(multiradix_state_t *state, int reg_in, int reg_out, int stride) {
    if (!state) return -1;
    if (reg_in < 0 || reg_in >= MR_NUM_REGS) return -1;
    if (reg_out < 0 || reg_out >= MR_NUM_REGS) return -1;
    if (stride <= 0) return -1;

    trit2_reg32 *in  = &state->regs[reg_in];
    trit2_reg32 out_tmp = trit2_reg32_splat(TRIT2_UNKNOWN);

    /*
     * Process groups of 3 trits with the given stride.
     * For each butterfly group at positions (i, i+stride, i+2*stride):
     *   out[0] = a + b + c              (mod 3 balanced)
     *   out[1] = a + ω·b + ω²·c
     *   out[2] = a + ω²·b + ω·c
     */
    int groups_done = 0;
    for (int base = 0; base + 2 * stride < MR_REG_WIDTH; base += 3 * stride) {
        int i0 = base;
        int i1 = base + stride;
        int i2 = base + 2 * stride;

        int a = trit2_decode(trit2_reg32_get(in, i0));
        int b = trit2_decode(trit2_reg32_get(in, i1));
        int c = trit2_decode(trit2_reg32_get(in, i2));

        /* Butterfly outputs (ternary DFT kernel) */
        int o0 = trit_add_mod3(trit_add_mod3(a, b), c);
        int o1 = trit_add_mod3(trit_add_mod3(a, trit_rotate(b)),
                               trit_rotate2(c));
        int o2 = trit_add_mod3(trit_add_mod3(a, trit_rotate2(b)),
                               trit_rotate(c));

        trit2_reg32_set(&out_tmp, i0, trit2_encode(o0));
        trit2_reg32_set(&out_tmp, i1, trit2_encode(o1));
        trit2_reg32_set(&out_tmp, i2, trit2_encode(o2));
        groups_done++;
    }

    state->regs[reg_out] = out_tmp;
    state->fft_stage++;

    state->lb_total_insns++;
    state->lb_trit_insns++;

    return groups_done;
}

/* ==== RADIX_CONV ======================================================= */

int radix_conv_to_ternary(multiradix_state_t *state, int reg, int value) {
    if (!state) return -1;
    if (reg < 0 || reg >= MR_NUM_REGS) return -1;

    /* Clear register */
    state->regs[reg] = trit2_reg32_splat(TRIT2_UNKNOWN);

    int n = value;
    int negative = (n < 0);
    if (negative) n = -n;

    int nonzero = 0;

    for (int pos = 0; pos < MR_REG_WIDTH && n != 0; pos++) {
        int r = n % 3;
        int tval;

        if (r == 0) {
            tval = 0;
            n = n / 3;
        } else if (r == 1) {
            tval = 1;
            n = (n - 1) / 3;
            nonzero++;
        } else {  /* r == 2 → balanced digit is -1, carry +1 */
            tval = -1;
            n = (n + 1) / 3;
            nonzero++;
        }

        if (negative) tval = -tval;  /* negate for negative input */
        trit2_reg32_set(&state->regs[reg], pos, trit2_encode(tval));
    }

    state->lb_total_insns++;

    return nonzero;
}

int radix_conv_to_binary(const multiradix_state_t *state, int reg, int width) {
    if (!state) return 0;
    if (reg < 0 || reg >= MR_NUM_REGS) return 0;
    if (width <= 0) return 0;
    if (width > MR_REG_WIDTH) width = MR_REG_WIDTH;

    const trit2_reg32 *r = &state->regs[reg];

    int result = 0;
    int power  = 1;  /* 3^pos */

    for (int pos = 0; pos < width; pos++) {
        int tval = trit2_decode(trit2_reg32_get(r, pos));
        result += tval * power;
        power *= 3;
    }

    return result;
}

/* ==== TRIT_LB (Load Balance Telemetry) ================================= */

void trit_lb_record(multiradix_state_t *state) {
    if (!state) return;
    state->lb_total_insns++;
    state->lb_trit_insns++;
}

void trit_lb_sparse_hit(multiradix_state_t *state) {
    if (!state) return;
    state->lb_sparse_hits++;
}

trit_lb_snapshot_t trit_lb_snapshot(const multiradix_state_t *state) {
    trit_lb_snapshot_t snap = { 0, 0, 0, 0, -1 };
    if (!state) return snap;

    snap.total_insns    = state->lb_total_insns;
    snap.thermal_events = state->lb_thermal_limit;

    if (state->lb_total_insns > 0) {
        snap.trit_ratio_pct =
            (state->lb_trit_insns * 100) / state->lb_total_insns;
    }
    if (state->lb_trit_insns > 0) {
        snap.sparse_ratio_pct =
            (state->lb_sparse_hits * 100) / state->lb_trit_insns;
    }

    /* Affinity heuristic: if >70% ternary, recommend trit core */
    if (snap.trit_ratio_pct > 70) {
        snap.suggested_affinity = 1;  /* trit-optimized core */
    } else if (snap.trit_ratio_pct < 30) {
        snap.suggested_affinity = 0;  /* binary core */
    } else {
        snap.suggested_affinity = -1; /* no preference */
    }

    return snap;
}

void trit_lb_reset(multiradix_state_t *state) {
    if (!state) return;
    state->lb_total_insns   = 0;
    state->lb_trit_insns    = 0;
    state->lb_sparse_hits   = 0;
    state->lb_thermal_limit = 0;
    state->lb_affinity_migr = 0;
}

/* ========================================================================
 * RNS (Residue Number System) — Output-Parameter API
 * ======================================================================== */

#include "set6/trit_rns.h"
#include <stdlib.h>
#include <string.h>

/* ---- Internal helpers ------------------------------------------------- */

/** Positive modulo: always returns [0, m). */
static uint32_t rns_posmod(int64_t a, uint32_t m) {
    int64_t r = a % (int64_t)m;
    return (uint32_t)(r < 0 ? r + (int64_t)m : r);
}

/**
 * @brief Modular inverse via Extended Euclidean Algorithm.
 * @param a  Value whose inverse is sought.
 * @param m  Modulus (must be > 0).
 * @return   a^(-1) mod m, or 0 if non-invertible.
 */
static uint32_t mod_inverse(uint32_t a, uint32_t m) {
    if (m <= 1) return 0;
    int64_t r0 = (int64_t)m, r1 = (int64_t)(a % m);
    int64_t s0 = 0,          s1 = 1;

    while (r1 != 0) {
        int64_t q = r0 / r1;
        int64_t tmp;
        tmp = r0 - q * r1; r0 = r1; r1 = tmp;
        tmp = s0 - q * s1; s0 = s1; s1 = tmp;
    }
    if (r0 != 1) return 0;  /* gcd ≠ 1 → non-invertible */
    return (uint32_t)((s0 % (int64_t)m + (int64_t)m) % (int64_t)m);
}

/** GCD for coprimality checks. */
static uint32_t rns_gcd(uint32_t a, uint32_t b) {
    while (b) { uint32_t t = b; b = a % b; a = t; }
    return a;
}

/* ---- 1. trit_rns_init ------------------------------------------------- */

int trit_rns_init(trit_rns_context_t *ctx) {
    if (!ctx) return -1;

    /* Set default moduli {3, 5, 7} */
    ctx->count = RNS_MODULI_COUNT;
    for (uint32_t i = 0; i < RNS_MODULI_COUNT; i++)
        ctx->moduli[i] = rns_initial_moduli[i];
    for (uint32_t i = RNS_MODULI_COUNT; i < RNS_MAX_MODULI; i++)
        ctx->moduli[i] = 0;

    /* Compute M = product of all moduli */
    ctx->M = 1;
    for (uint32_t i = 0; i < ctx->count; i++)
        ctx->M *= ctx->moduli[i];

    /* Precompute Mi = M / moduli[i], Mi_inv = Mi^(-1) mod moduli[i] */
    for (uint32_t i = 0; i < ctx->count; i++) {
        ctx->Mi[i]     = ctx->M / ctx->moduli[i];
        ctx->Mi_inv[i] = mod_inverse(ctx->Mi[i], ctx->moduli[i]);
        if (ctx->Mi_inv[i] == 0) return -1;  /* non-coprime */
    }

    /* Zero unused slots */
    for (uint32_t i = ctx->count; i < RNS_MAX_MODULI; i++) {
        ctx->Mi[i]     = 0;
        ctx->Mi_inv[i] = 0;
    }

    return 0;
}

/* ---- 2. trit_to_rns (output-param, ctx-last) -------------------------- */

void trit_to_rns(const trit2_reg32 *trit_vec, int n_trits,
                  trit_rns_t *rns_out, const trit_rns_context_t *ctx) {
    if (!rns_out) return;
    memset(rns_out, 0, sizeof(*rns_out));
    if (!trit_vec || !ctx || n_trits <= 0) return;
    if (n_trits > 32) n_trits = 32;

    /*
     * Evaluate value = Σ decode(trit[i]) × 3^i  modularly per channel.
     * Uses Horner's method in reverse: accumulate from MSB to LSB.
     *   acc = 0; for i = n-1 downto 0: acc = acc*3 + trit[i]  (mod m)
     */
    for (uint32_t ch = 0; ch < ctx->count; ch++) {
        uint32_t m = ctx->moduli[ch];
        int64_t  acc = 0;
        for (int i = n_trits - 1; i >= 0; i--) {
            trit2 packed = trit2_reg32_get(trit_vec, i);
            int   val    = trit2_decode(packed);  /* -1, 0, +1 */
            acc = rns_posmod(acc * 3 + val, m);
        }
        rns_out->residues[ch] = (uint32_t)acc;
    }
}

/* ---- 3. rns_to_trit (output-param, ctx-last) -------------------------- */

void rns_to_trit(const trit_rns_t *rns_in, int n_trits,
                  trit2_reg32 *trit_out, const trit_rns_context_t *ctx) {
    if (!trit_out) return;
    *trit_out = trit2_reg32_splat(TRIT2_UNKNOWN);
    if (!rns_in || !ctx) return;
    if (n_trits <= 0) n_trits = 1;
    if (n_trits > 32) n_trits = 32;

    /* CRT reconstruction: x = Σ (r[i] × Mi[i] × Mi_inv[i]) mod M */
    int64_t x = 0;
    for (uint32_t i = 0; i < ctx->count; i++) {
        x += (int64_t)rns_in->residues[i] * ctx->Mi[i] * ctx->Mi_inv[i];
    }
    int value = (int)(x % (int64_t)ctx->M);
    if (value < 0) value += (int)ctx->M;

    /* Signed representation: map to [-M/2, M/2] */
    if (value > (int)RNS_HALF_RANGE)
        value -= (int)ctx->M;

    /* Balanced-ternary decomposition */
    int remaining = value;
    int negative  = (remaining < 0);
    if (negative) remaining = -remaining;

    for (int i = 0; i < n_trits; i++) {
        int digit = remaining % 3;
        remaining /= 3;
        if (digit == 2) {
            digit = -1;
            remaining += 1;
        }
        if (negative) digit = -digit;
        trit2 encoded = trit2_encode(digit);
        trit2_reg32_set(trit_out, i, encoded);
    }
}

/* ---- 4. rns_add (output-param, ctx-last) ------------------------------ */

void rns_add(const trit_rns_t *a, const trit_rns_t *b,
              trit_rns_t *out, const trit_rns_context_t *ctx) {
    if (!out) return;
    memset(out, 0, sizeof(*out));
    if (!a || !b || !ctx) return;

    for (uint32_t i = 0; i < ctx->count; i++) {
        out->residues[i] = (a->residues[i] + b->residues[i])
                           % ctx->moduli[i];
    }
}

/* ---- 5. rns_sub (output-param, ctx-last) ------------------------------ */

void rns_sub(const trit_rns_t *a, const trit_rns_t *b,
              trit_rns_t *out, const trit_rns_context_t *ctx) {
    if (!out) return;
    memset(out, 0, sizeof(*out));
    if (!a || !b || !ctx) return;

    for (uint32_t i = 0; i < ctx->count; i++) {
        out->residues[i] = rns_posmod((int64_t)a->residues[i]
                                     - (int64_t)b->residues[i],
                                      ctx->moduli[i]);
    }
}

/* ---- 6. rns_mul (output-param, ctx-last) ------------------------------ */

void rns_mul(const trit_rns_t *a, const trit_rns_t *b,
              trit_rns_t *out, const trit_rns_context_t *ctx) {
    if (!out) return;
    memset(out, 0, sizeof(*out));
    if (!a || !b || !ctx) return;

    for (uint32_t i = 0; i < ctx->count; i++) {
        out->residues[i] = (uint32_t)(((uint64_t)a->residues[i]
                                      * b->residues[i])
                                      % ctx->moduli[i]);
    }
}

/* ---- 7. rns_montgomery_mul (output-param, ctx-last) ------------------- */

void rns_montgomery_mul(const trit_rns_t *a, const trit_rns_t *b,
                          trit_rns_t *out, const trit_rns_context_t *ctx) {
    if (!out) return;
    memset(out, 0, sizeof(*out));
    if (!a || !b || !ctx) return;

    for (uint32_t i = 0; i < ctx->count; i++) {
        uint32_t mi = ctx->moduli[i];

        /* Ternary-aligned R: smallest power of 3 > mi */
        uint32_t R = 3;
        while (R <= mi) R *= 3;

        /* N' = -mi^(-1) mod R */
        uint32_t mi_inv_R = mod_inverse(mi, R);
        if (mi_inv_R == 0) {
            /* Fallback to plain modular mul */
            out->residues[i] = (uint32_t)(((uint64_t)a->residues[i]
                                          * b->residues[i]) % mi);
            continue;
        }
        uint32_t N_prime = rns_posmod(-(int64_t)mi_inv_R, R);

        /* REDC: t = a*b, u = (t * N') mod R, res = (t + u*mi) / R */
        uint64_t t = (uint64_t)a->residues[i] * b->residues[i];
        uint64_t u = (t * N_prime) % R;
        uint64_t s = (t + u * mi) / R;

        if (s >= mi) s -= mi;
        out->residues[i] = (uint32_t)s;
    }
}

/* ---- 8. rns_is_zero (ctx-last) ---------------------------------------- */

bool rns_is_zero(const trit_rns_t *rns, const trit_rns_context_t *ctx) {
    if (!rns || !ctx) return false;
    for (uint32_t i = 0; i < ctx->count; i++) {
        if (rns->residues[i] != 0) return false;
    }
    return true;
}

/* ---- 9. rns_validate (rns first, ctx second) -------------------------- */

int rns_validate(const trit_rns_t *rns, const trit_rns_context_t *ctx) {
    if (!rns || !ctx) return -1;

    /* Check each residue is in [0, moduli[i]) */
    for (uint32_t i = 0; i < ctx->count; i++) {
        if (rns->residues[i] >= ctx->moduli[i]) return -1;
    }

    /* CRT round-trip: reconstruct → decompose → compare */
    int64_t x = 0;
    for (uint32_t i = 0; i < ctx->count; i++) {
        x += (int64_t)rns->residues[i] * ctx->Mi[i] * ctx->Mi_inv[i];
    }
    uint32_t recon = (uint32_t)(x % (int64_t)ctx->M);

    for (uint32_t i = 0; i < ctx->count; i++) {
        if (recon % ctx->moduli[i] != rns->residues[i]) return -1;
    }

    return 0;
}

/* ---- 10. rns_extend_moduli -------------------------------------------- */

int rns_extend_moduli(trit_rns_context_t *ctx, uint32_t new_modulus) {
    if (!ctx) return -1;
    if (ctx->count >= RNS_MAX_MODULI) return -1;
    if (new_modulus <= 1) return -1;

    /* Verify coprimality with all existing moduli */
    for (uint32_t i = 0; i < ctx->count; i++) {
        if (rns_gcd(ctx->moduli[i], new_modulus) != 1) return -1;
    }

    /* Add the new modulus */
    ctx->moduli[ctx->count] = new_modulus;
    ctx->count++;

    /* Recompute M */
    ctx->M = 1;
    for (uint32_t i = 0; i < ctx->count; i++)
        ctx->M *= ctx->moduli[i];

    /* Recompute Mi and Mi_inv for ALL channels */
    for (uint32_t i = 0; i < ctx->count; i++) {
        ctx->Mi[i]     = ctx->M / ctx->moduli[i];
        ctx->Mi_inv[i] = mod_inverse(ctx->Mi[i], ctx->moduli[i]);
        if (ctx->Mi_inv[i] == 0) return -1;
    }

    return 0;
}

/* ---- 11. rns_apply_noise (PVT resilience) ----------------------------- */

void rns_apply_noise(trit_rns_t *rns, double noise_prob,
                       const trit_rns_context_t *ctx) {
    if (!rns || !ctx) return;
    if (noise_prob <= 0.0) return;

    for (uint32_t i = 0; i < ctx->count; i++) {
        double r = (double)rand() / (double)RAND_MAX;
        if (r < noise_prob) {
            /* Replace residue with random value in [0, moduli[i]) */
            rns->residues[i] = (uint32_t)(rand() % ctx->moduli[i]);
        }
    }
}

/* ---- 12. trit_rns_init_custom ----------------------------------------- */

int trit_rns_init_custom(trit_rns_context_t *ctx,
                         const uint32_t *moduli, uint32_t count) {
    if (!ctx || !moduli || count == 0 || count > RNS_MAX_MODULI) return -1;

    /* Verify pairwise coprimality */
    for (uint32_t i = 0; i < count; i++) {
        if (moduli[i] <= 1) return -1;
        for (uint32_t j = i + 1; j < count; j++) {
            if (rns_gcd(moduli[i], moduli[j]) != 1) return -1;
        }
    }

    ctx->count = count;
    for (uint32_t i = 0; i < count; i++)
        ctx->moduli[i] = moduli[i];
    for (uint32_t i = count; i < RNS_MAX_MODULI; i++)
        ctx->moduli[i] = 0;

    ctx->M = 1;
    for (uint32_t i = 0; i < ctx->count; i++)
        ctx->M *= ctx->moduli[i];

    for (uint32_t i = 0; i < ctx->count; i++) {
        ctx->Mi[i]     = ctx->M / ctx->moduli[i];
        ctx->Mi_inv[i] = mod_inverse(ctx->Mi[i], ctx->moduli[i]);
        if (ctx->Mi_inv[i] == 0) return -1;
    }
    for (uint32_t i = ctx->count; i < RNS_MAX_MODULI; i++) {
        ctx->Mi[i] = 0;
        ctx->Mi_inv[i] = 0;
    }

    return 0;
}

/* ---- 13. rns_to_mrs (Mixed-Radix System conversion) ------------------- */

int rns_to_mrs(const trit_rns_t *rns, uint32_t *digits,
               const trit_rns_context_t *ctx) {
    if (!rns || !digits || !ctx) return -1;

    uint32_t v[RNS_MAX_MODULI];
    for (uint32_t i = 0; i < ctx->count; i++)
        v[i] = rns->residues[i];

    for (uint32_t i = 0; i < ctx->count; i++) {
        digits[i] = v[i];
        for (uint32_t j = i + 1; j < ctx->count; j++) {
            uint32_t mi = ctx->moduli[i];
            uint32_t mj = ctx->moduli[j];
            uint32_t mi_inv_mj = mod_inverse(mi, mj);
            if (mi_inv_mj == 0) return -1;
            int64_t diff = (int64_t)v[j] - (int64_t)digits[i];
            v[j] = (uint32_t)rns_posmod(diff * (int64_t)mi_inv_mj, mj);
        }
    }
    return 0;
}

/* ---- 14. rns_from_mrs ------------------------------------------------- */

int rns_from_mrs(const uint32_t *digits, trit_rns_t *rns_out,
                 const trit_rns_context_t *ctx) {
    if (!digits || !rns_out || !ctx) return -1;

    uint64_t x = 0;
    uint64_t weight = 1;
    for (uint32_t i = 0; i < ctx->count; i++) {
        x += (uint64_t)digits[i] * weight;
        weight *= ctx->moduli[i];
    }

    for (uint32_t i = 0; i < ctx->count; i++)
        rns_out->residues[i] = (uint32_t)(x % ctx->moduli[i]);

    return 0;
}

/* ---- 15. rns_montgomery_exp ------------------------------------------- */

int rns_montgomery_exp(const trit_rns_t *base, uint32_t exp,
                       trit_rns_t *out, const trit_rns_context_t *ctx) {
    if (!base || !out || !ctx) return -1;

    trit_rns_t result;
    for (uint32_t i = 0; i < ctx->count; i++)
        result.residues[i] = 1 % ctx->moduli[i];
    for (uint32_t i = ctx->count; i < RNS_MAX_MODULI; i++)
        result.residues[i] = 0;

    trit_rns_t b = *base;
    uint32_t e = exp;

    while (e > 0) {
        if (e & 1) {
            trit_rns_t tmp;
            rns_montgomery_mul(&result, &b, &tmp, ctx);
            result = tmp;
        }
        trit_rns_t sq;
        rns_montgomery_mul(&b, &b, &sq, ctx);
        b = sq;
        e >>= 1;
    }

    *out = result;
    return 0;
}

/* ---- 16. rns_gcd_public ---------------------------------------------- */

uint32_t rns_gcd_public(uint32_t a, uint32_t b) {
    return rns_gcd(a, b);
}

/* ---- 17. rns_add_redundant_check ------------------------------------- */

static int mrx_is_prime(uint32_t n) {
    if (n < 2) return 0;
    if (n < 4) return 1;
    if (n % 2 == 0 || n % 3 == 0) return 0;
    for (uint32_t i = 5; (uint64_t)i * i <= n; i += 6) {
        if (n % i == 0 || n % (i + 2) == 0) return 0;
    }
    return 1;
}

int rns_add_redundant_check(trit_rns_context_t *ctx) {
    if (!ctx) return -1;
    if (ctx->count >= RNS_MAX_MODULI) return -1;

    uint32_t candidate = ctx->moduli[ctx->count - 1] + 1;
    for (;;) {
        if (mrx_is_prime(candidate)) {
            int coprime = 1;
            for (uint32_t i = 0; i < ctx->count; i++) {
                if (rns_gcd(ctx->moduli[i], candidate) != 1) {
                    coprime = 0;
                    break;
                }
            }
            if (coprime) break;
        }
        candidate++;
        if (candidate > 1000000) return -1;
    }

    return rns_extend_moduli(ctx, candidate);
}

/* ---- 18. rns_detect_correct ------------------------------------------ */

int rns_detect_correct(const trit_rns_t *rns, trit_rns_t *corrected,
                       const trit_rns_context_t *ctx) {
    if (!rns || !corrected || !ctx) return -1;
    if (ctx->count < 2) return -1;

    *corrected = *rns;

    /* CRT reconstruction */
    int64_t x_full = 0;
    for (uint32_t i = 0; i < ctx->count; i++) {
        x_full += (int64_t)rns->residues[i] * ctx->Mi[i] * ctx->Mi_inv[i];
    }
    uint32_t recon_full = (uint32_t)(x_full % (int64_t)ctx->M);

    int error_channel = -1;
    int error_count = 0;
    for (uint32_t i = 0; i < ctx->count; i++) {
        if (recon_full % ctx->moduli[i] != rns->residues[i]) {
            error_channel = (int)i;
            error_count++;
        }
    }

    if (error_count == 0) return 0;  /* No error */

    if (error_count == 1 && ctx->count >= 4) {
        corrected->residues[error_channel] =
            recon_full % ctx->moduli[error_channel];
        return 1;  /* Corrected */
    }

    return -1;  /* Uncorrectable */
}
