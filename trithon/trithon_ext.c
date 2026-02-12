/**
 * @file trithon_ext.c
 * @brief Trithon C Extension — Native trit ops for Python CFFI.
 *
 * Compiled to libtrithon.so, loaded by trithon.py via ctypes.
 * Wraps the real seT5 trit.h / multiradix.h / trit_emu.h APIs so
 * Python gets zero-overhead access to Kleene K₃ logic, balanced
 * ternary arithmetic, DOT_TRIT, FFT_STEP, and packed SIMD.
 *
 * Build:
 *   gcc -shared -fPIC -O2 -Iinclude -Itools/compiler/include \
 *       -o trithon/libtrithon.so trithon/trithon_ext.c \
 *       src/multiradix.c
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <string.h>
#include <stdint.h>
#include "set5/trit.h"
#include "set5/trit_emu.h"
#include "set5/trit_cast.h"
#include "set5/multiradix.h"

/* ===================================================================== */
/*  1.  Scalar Trit Operations                                           */
/* ===================================================================== */

/** Kleene AND = min(a, b) */
int8_t trithon_and(int8_t a, int8_t b) {
    return trit_and((trit)a, (trit)b);
}

/** Kleene OR = max(a, b) */
int8_t trithon_or(int8_t a, int8_t b) {
    return trit_or((trit)a, (trit)b);
}

/** Kleene NOT = -a */
int8_t trithon_not(int8_t a) {
    return trit_not((trit)a);
}

/** Kleene IMPLIES = max(-a, b) */
int8_t trithon_implies(int8_t a, int8_t b) {
    return trit_implies((trit)a, (trit)b);
}

/** Kleene EQUIV = and(implies(a,b), implies(b,a)) */
int8_t trithon_equiv(int8_t a, int8_t b) {
    return trit_equiv((trit)a, (trit)b);
}

/**
 * Balanced ternary increment with cyclic wrap.
 *   -1 → 0 → +1 → -1 (carry)
 */
int8_t trithon_inc(int8_t t) {
    if (t >= 1) return -1;  /* +1 wraps to -1 */
    return (int8_t)(t + 1);
}

/**
 * Balanced ternary decrement with cyclic wrap.
 *   +1 → 0 → -1 → +1 (borrow)
 */
int8_t trithon_dec(int8_t t) {
    if (t <= -1) return 1;  /* -1 wraps to +1 */
    return (int8_t)(t - 1);
}

/** Consensus = Kleene AND (alias for clarity) */
int8_t trithon_consensus(int8_t a, int8_t b) {
    return trit_and((trit)a, (trit)b);
}

/** Accept-any = Kleene OR (alias for clarity) */
int8_t trithon_accept_any(int8_t a, int8_t b) {
    return trit_or((trit)a, (trit)b);
}

/** Balanced ternary multiplication: a * b */
int8_t trithon_mul(int8_t a, int8_t b) {
    /* For trits {-1,0,+1}, standard int multiply is correct */
    int r = (int)a * (int)b;
    return (int8_t)r;
}

/** Safe collapse to boolean: Unknown → 0 (false) */
int trithon_to_bool(int8_t t) {
    return trit_to_bool_safe((trit)t);
}

/** Is definite (not Unknown)? */
int trithon_is_definite(int8_t t) {
    return trit_is_definite((trit)t);
}

/* ===================================================================== */
/*  2.  Array Operations (trit vectors)                                  */
/* ===================================================================== */

/**
 * Element-wise Kleene AND on two trit arrays.
 * @param out  Output array (pre-allocated, size n).
 * @param a    First input array.
 * @param b    Second input array.
 * @param n    Array length.
 */
void trithon_array_and(int8_t *out, const int8_t *a, const int8_t *b, int n) {
    for (int i = 0; i < n; i++)
        out[i] = trit_and(a[i], b[i]);
}

/** Element-wise Kleene OR */
void trithon_array_or(int8_t *out, const int8_t *a, const int8_t *b, int n) {
    for (int i = 0; i < n; i++)
        out[i] = trit_or(a[i], b[i]);
}

/** Element-wise Kleene NOT */
void trithon_array_not(int8_t *out, const int8_t *a, int n) {
    for (int i = 0; i < n; i++)
        out[i] = trit_not(a[i]);
}

/**
 * Balanced ternary dot product on raw trit arrays.
 * DOT = Σ (a_i * b_i)  where * is trit multiplication.
 *
 * For ternary weight networks (TWN/TTQ), this reduces to
 * additions and sign flips — no multiplies needed.
 */
int trithon_dot(const int8_t *a, const int8_t *b, int n) {
    int acc = 0;
    for (int i = 0; i < n; i++)
        acc += (int)a[i] * (int)b[i];
    return acc;
}

/**
 * N:M structured sparsity dot product.
 * In each N-element block, only non-zero trits are multiplied.
 */
int trithon_dot_sparse(const int8_t *a, const int8_t *b,
                       int n, int block_n, int block_m) {
    (void)block_m;  /* block_m used for validation only */
    int acc = 0;
    for (int i = 0; i < n; i += block_n) {
        for (int j = 0; j < block_n && (i + j) < n; j++) {
            if (a[i + j] != 0)
                acc += (int)a[i + j] * (int)b[i + j];
        }
    }
    return acc;
}

/**
 * Radix-3 FFT butterfly step on 3 consecutive trits.
 *
 *   Y0 = clamp(X0 + X1 + X2)
 *   Y1 = clamp(X0 + rot(X1) + rot²(X2))
 *   Y2 = clamp(X0 + rot²(X1) + rot(X2))
 *
 * where rot(v) = cyclic (-1→0→+1→-1)
 */
void trithon_fft_step(int8_t *arr, int offset, int size) {
    if (offset + 3 > size) return;

    int8_t x0 = arr[offset], x1 = arr[offset + 1], x2 = arr[offset + 2];

    /* Cyclic rotation in {-1, 0, +1} */
    #define ROT(v) ((int8_t)(((int)(v) + 2) % 3 - 1))
    #define ROT2(v) ROT(ROT(v))
    #define CLAMP(v) ((int8_t)((v) > 1 ? 1 : ((v) < -1 ? -1 : (v))))

    arr[offset]     = CLAMP(x0 + x1 + x2);
    arr[offset + 1] = CLAMP(x0 + ROT(x1) + ROT2(x2));
    arr[offset + 2] = CLAMP(x0 + ROT2(x1) + ROT(x2));

    #undef ROT
    #undef ROT2
    #undef CLAMP
}

/**
 * Balanced ternary increment on a trit array (multi-trit number).
 * Propagates carry from LST (index 0) upward.
 */
void trithon_array_inc(int8_t *arr, int n) {
    int carry = 1;
    for (int i = 0; i < n && carry; i++) {
        int v = (int)arr[i] + carry;
        if (v > 1) { arr[i] = -1; carry = 1; }
        else       { arr[i] = (int8_t)v; carry = 0; }
    }
}

/**
 * Balanced ternary decrement on a trit array (multi-trit number).
 */
void trithon_array_dec(int8_t *arr, int n) {
    int borrow = 1;
    for (int i = 0; i < n && borrow; i++) {
        int v = (int)arr[i] - borrow;
        if (v < -1) { arr[i] = 1; borrow = 1; }
        else        { arr[i] = (int8_t)v; borrow = 0; }
    }
}

/**
 * Convert integer to balanced ternary array (Avizienis algorithm).
 * @param out   Output array (pre-allocated, width trits).
 * @param value Integer to convert.
 * @param width Number of trits.
 */
void trithon_from_int(int8_t *out, int value, int width) {
    int v = value;
    for (int i = 0; i < width; i++) {
        int r = v % 3;
        if (r < 0) r += 3;  /* C modulo can be negative */
        if (r == 2) {
            out[i] = -1;
            v = (v + 1) / 3;
        } else {
            out[i] = (int8_t)r;
            v = v / 3;
        }
    }
}

/**
 * Convert balanced ternary array back to integer.
 */
int trithon_to_int(const int8_t *arr, int width) {
    int result = 0;
    for (int i = width - 1; i >= 0; i--)
        result = result * 3 + (int)arr[i];
    return result;
}

/**
 * Compute sparsity (fraction of zero trits).
 * Returns value * 1000 (permille) to avoid floating point.
 */
int trithon_sparsity_permille(const int8_t *arr, int n) {
    if (n == 0) return 0;
    int zeros = 0;
    for (int i = 0; i < n; i++)
        if (arr[i] == 0) zeros++;
    return (zeros * 1000) / n;
}

/**
 * Census: count F/U/T trits.
 * out[0] = F count, out[1] = U count, out[2] = T count.
 */
void trithon_census(const int8_t *arr, int n, int *out) {
    out[0] = out[1] = out[2] = 0;
    for (int i = 0; i < n; i++) {
        if (arr[i] == -1) out[0]++;
        else if (arr[i] == 0) out[1]++;
        else out[2]++;
    }
}

/* ===================================================================== */
/*  3.  SIMD Packed Operations (64-bit / 32 trits)                       */
/* ===================================================================== */

/** Packed Kleene AND on 32 trits (2 bits each) */
uint64_t trithon_packed_and(uint64_t a, uint64_t b) {
    return trit_and_packed64(a, b);
}

/** Packed Kleene OR */
uint64_t trithon_packed_or(uint64_t a, uint64_t b) {
    return trit_or_packed64(a, b);
}

/** Packed Kleene NOT */
uint64_t trithon_packed_not(uint64_t a) {
    return trit_not_packed64(a);
}

/* ===================================================================== */
/*  4.  Multi-Radix Engine Bridge                                        */
/* ===================================================================== */

/**
 * Full multi-radix DOT_TRIT via the seT5 engine.
 * Loads two arrays into MR registers, computes dot product.
 *
 * @param a, b   Trit arrays (max 32 elements used).
 * @param n      Array length (capped at 32).
 * @return       Dot product value.
 */
int trithon_mr_dot(const int8_t *a, const int8_t *b, int n) {
    multiradix_state_t mr;
    multiradix_init(&mr);

    int lim = (n > 32) ? 32 : n;
    for (int i = 0; i < lim; i++) {
        trit2 ta = (a[i] == 1) ? TRIT2_TRUE :
                   (a[i] == -1) ? TRIT2_FALSE : TRIT2_UNKNOWN;
        trit2 tb = (b[i] == 1) ? TRIT2_TRUE :
                   (b[i] == -1) ? TRIT2_FALSE : TRIT2_UNKNOWN;
        trit2_reg32_set(&mr.regs[0], i, ta);
        trit2_reg32_set(&mr.regs[1], i, tb);
    }

    return dot_trit(&mr, 0, 1);
}

/**
 * Full multi-radix FFT_STEP via the seT5 engine.
 * Loads array into MR register, runs butterfly, extracts result.
 *
 * @param arr    Trit array (in/out, max 32 elements).
 * @param n      Array length (capped at 32).
 * @param stride FFT stride.
 */
void trithon_mr_fft(int8_t *arr, int n, int stride) {
    multiradix_state_t mr;
    multiradix_init(&mr);

    int lim = (n > 32) ? 32 : n;
    for (int i = 0; i < lim; i++) {
        trit2 t = (arr[i] == 1) ? TRIT2_TRUE :
                  (arr[i] == -1) ? TRIT2_FALSE : TRIT2_UNKNOWN;
        trit2_reg32_set(&mr.regs[0], i, t);
    }

    fft_step(&mr, 0, 1, stride);

    for (int i = 0; i < lim; i++) {
        trit2 t = trit2_reg32_get(&mr.regs[1], i);
        arr[i] = trit2_to_trit(t);
    }
}

/**
 * Radix conversion: integer → balanced ternary via MR engine.
 * @param out   Output trit array (max 32).
 * @param value Integer to convert.
 * @param width Number of trits to extract.
 */
void trithon_mr_radix_conv(int8_t *out, int value, int width) {
    multiradix_state_t mr;
    multiradix_init(&mr);
    radix_conv_to_ternary(&mr, 0, value);

    int lim = (width > 32) ? 32 : width;
    for (int i = 0; i < lim; i++) {
        trit2 t = trit2_reg32_get(&mr.regs[0], i);
        out[i] = trit2_to_trit(t);
    }
}

/* ===================================================================== */
/*  5.  Version / Diagnostics                                            */
/* ===================================================================== */

/** Return library version as integer: major*100 + minor */
int trithon_version(void) {
    return 200;  /* 2.00 — CFFI extension */
}

/** Return number of trits per SIMD word */
int trithon_simd_width(void) {
    return 32;  /* 64 bits / 2 bits per trit */
}
