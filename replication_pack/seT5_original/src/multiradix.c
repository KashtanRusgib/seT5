/**
 * @file multiradix.c
 * @brief seT5 Multi-Radix Instructions — Implementation
 *
 * Implements DOT_TRIT, FFT_STEP, RADIX_CONV, and TRIT_LB instructions
 * for the seT5 balanced ternary microkernel.
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
 * @see include/set5/multiradix.h for full API documentation
 * @see ARCHITECTURE.md §6 for hardware alignment details
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/multiradix.h"
#include "set5/trit_cast.h"
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
