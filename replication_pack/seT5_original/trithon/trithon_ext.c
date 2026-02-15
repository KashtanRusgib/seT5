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
#include "set5/ternary_weight_quantizer.h"
#include "set5/dlfet_sim.h"
#include "set5/radix_transcode.h"
#include "set5/srbc.h"
#include "set5/trit_crypto.h"
#include "set5/prop_delay.h"
#include "set5/ternary_temporal.h"
#include "set5/pam3_transcode.h"
#include "set5/stt_mram.h"
#include "set5/tipc.h"
#include "set5/tfs.h"

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

/**
 * Balanced ternary division: a / b.
 * For trits {-1,0,+1}, division is a*b when b≠0 (since 1/1=1, 1/(-1)=-1).
 * Division by Unknown (0) returns Unknown (safe default).
 */
int8_t trithon_div(int8_t a, int8_t b) {
    if (b == 0) return 0;           /* div by Unknown → Unknown */
    return (int8_t)((int)a * (int)b); /* a / {±1} = a * {±1} */
}

/**
 * Balanced ternary exponentiation: base ^ exp.
 * Truth table for trits:
 *   T^T=T  T^U=T  T^F=T   (1 to any power is 1)
 *   U^T=U  U^U=T  U^F=U   (0^0=1 by convention, 0^neg=undef→U)
 *   F^T=F  F^U=T  F^F=F   ((-1)^1=-1, (-1)^0=1, (-1)^(-1)=-1)
 */
int8_t trithon_pow(int8_t base, int8_t exp) {
    if (exp == 0) return 1;           /* anything^0 = T (by convention) */
    if (base == 0) return 0;          /* U^{pos or neg} = U */
    if (base == 1) return 1;          /* T^anything = T */
    /* base == -1 */
    if (exp == 1) return -1;          /* F^T = F */
    /* exp == -1: F^F = (-1)^(-1) = 1/(-1) = -1 = F */
    return -1;
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

/* ===================================================================== */
/*  6.  Functional Utility Module Wrappers                               */
/* ===================================================================== */

/* ---- TWQ (Ternary Weight Quantizer) ---- */

/**
 * Quantize integer weights (×1000) to ternary {-1,0,+1}.
 * @param out      Output trit array.
 * @param weights  Input weights (×1000 fixed-point).
 * @param count    Number of weights.
 * @return         0 on success.
 */
int trithon_twq_quantize(int8_t *out, const int32_t *weights, int count) {
    if (count <= 0 || count > TWQ_MAX_WEIGHTS) return -1;
    twq_config_t cfg;
    twq_config_init(&cfg);
    twq_layer_t layer;
    int rc = twq_quantize(&layer, weights, count, &cfg);
    if (rc != 0) return rc;
    for (int i = 0; i < count; i++) {
        out[i] = (int8_t)layer.weights[i];
    }
    return 0;
}

/** Ternary dot product */
int trithon_twq_dot(const int8_t *a, const int8_t *b, int len) {
    return twq_ternary_dot((const trit *)a, (const trit *)b, len);
}

/** Energy ratio estimate (×1000 vs FP16) */
int trithon_twq_energy_ratio(const int8_t *weights, int count) {
    twq_config_t cfg;
    twq_config_init(&cfg);
    twq_layer_t layer;
    if (twq_quantize(&layer, NULL, 0, &cfg) != 0) {
        /* Build layer manually from pre-quantized trits */
        layer.count = count > TWQ_MAX_WEIGHTS ? TWQ_MAX_WEIGHTS : count;
        for (int i = 0; i < layer.count; i++)
            layer.weights[i] = (trit)weights[i];
        layer.stats.zero_count = 0;
        layer.stats.total_weights = layer.count;
        for (int i = 0; i < layer.count; i++)
            if (layer.weights[i] == 0) layer.stats.zero_count++;
        layer.stats.sparsity_permille = (layer.stats.zero_count * 1000) / layer.count;
    }
    return twq_energy_ratio(&layer);
}

/* ---- DLFET-RM Simulator ---- */

/** DLFET TNOT gate */
int trithon_dlfet_tnot(int a) {
    dlfet_sim_state_t st;
    dlfet_sim_init(&st);
    return (int)dlfet_tnot(&st, (uint8_t)a);
}

/** DLFET TNAND gate */
int trithon_dlfet_tnand(int a, int b) {
    dlfet_sim_state_t st;
    dlfet_sim_init(&st);
    return (int)dlfet_tnand(&st, (uint8_t)a, (uint8_t)b);
}

/** DLFET Full Adder: returns sum in low byte, carry in high byte */
int trithon_dlfet_full_adder(int a, int b, int cin) {
    dlfet_sim_state_t st;
    dlfet_sim_init(&st);
    uint8_t sum, cout;
    dlfet_ternary_full_adder(&st, (uint8_t)a, (uint8_t)b, (uint8_t)cin,
                              &sum, &cout);
    return (int)sum | ((int)cout << 8);
}

/* ---- Radix Transcode ---- */

/** Integer → balanced ternary */
int trithon_rtc_to_ternary(int8_t *out, int value, int width) {
    return rtc_int_to_ternary((trit *)out, value, width, NULL);
}

/** Balanced ternary → integer */
int trithon_rtc_to_int(const int8_t *trits, int width) {
    return rtc_ternary_to_int((const trit *)trits, width, NULL);
}

/* ---- SRBC ---- */

/** Run SRBC for N ticks, return stability percentage */
int trithon_srbc_stability(int ticks, int thermal_delta_mc) {
    srbc_state_t st;
    srbc_init(&st);
    if (thermal_delta_mc != 0)
        srbc_apply_thermal(&st, thermal_delta_mc);
    for (int i = 0; i < ticks; i++)
        srbc_tick(&st);
    return srbc_get_stability(&st);
}

/* ---- Crypto ---- */

/** One-shot hash of trit array */
void trithon_crypto_hash(int8_t *digest, const int8_t *msg, int len) {
    tcrypto_hash((trit *)digest, (const trit *)msg, len);
}

/** Encrypt/decrypt roundtrip test: returns 1 if roundtrip OK */
int trithon_crypto_roundtrip(int8_t *data, int len, uint32_t seed) {
    int8_t original[TCRYPTO_MAX_MSG];
    if (len > TCRYPTO_MAX_MSG) len = TCRYPTO_MAX_MSG;
    memcpy(original, data, len);

    tcrypto_key_t key;
    tcrypto_keygen(&key, seed);
    trit iv[TCRYPTO_MAC_TRITS];
    memset(iv, 0, sizeof(iv));

    tcrypto_cipher_t c;
    tcrypto_cipher_init(&c, &key, iv, 4);
    tcrypto_encrypt(&c, (trit *)data, len);

    tcrypto_cipher_init(&c, &key, iv, 4);
    tcrypto_decrypt(&c, (trit *)data, len);

    return (memcmp(data, original, len) == 0) ? 1 : 0;
}

/* ---- Propagation Delay ---- */

/** Get nominal delay in picoseconds */
int trithon_pdelay_nominal(int from, int to) {
    return pdelay_get_nominal(from, to);
}

/* ---- TTL ---- */

/** Evaluate ALWAYS over a trit trace, return trit result */
int8_t trithon_ttl_always(const int8_t *trace, int len) {
    ttl_state_t st;
    ttl_init(&st);
    int p = ttl_register_prop(&st, "py_trace");
    for (int i = 0; i < len; i++) {
        ttl_observe(&st, p, (trit)trace[i]);
        ttl_advance(&st);
    }
    return (int8_t)ttl_always(&st, p);
}

/** Evaluate EVENTUALLY over a trit trace */
int8_t trithon_ttl_eventually(const int8_t *trace, int len) {
    ttl_state_t st;
    ttl_init(&st);
    int p = ttl_register_prop(&st, "py_trace");
    for (int i = 0; i < len; i++) {
        ttl_observe(&st, p, (trit)trace[i]);
        ttl_advance(&st);
    }
    return (int8_t)ttl_eventually(&st, p);
}

/* ---- PAM-3 ---- */

/** PAM-3 encode+decode roundtrip: returns 1 if lossless */
int trithon_pam3_roundtrip(const int8_t *trits, int count) {
    pam3_frame_t frame;
    pam3_encode(&frame, (const trit *)trits, count, NULL);
    int8_t out[PAM3_MAX_TRITS];
    pam3_decode((trit *)out, &frame, NULL);
    for (int i = 0; i < count; i++) {
        if (out[i] != trits[i]) return 0;
    }
    return 1;
}

/** PAM-3 bandwidth gain ×10 */
int trithon_pam3_bandwidth_gain(int trit_count) {
    return pam3_bandwidth_gain(trit_count);
}

/* ===================================================================== */
/*  7.  STT-MRAM Module Wrappers                                        */
/* ===================================================================== */

/** MRAM pack 5 trits → byte */
int trithon_mram_pack(const int8_t *trits) {
    return (int)mram_pack_trits((const trit *)trits);
}

/** MRAM unpack byte → 5 trits */
void trithon_mram_unpack(int byte_val, int8_t *trits) {
    mram_unpack_trits((uint8_t)byte_val, (trit *)trits);
}

/** MRAM pack/unpack roundtrip: returns 1 if lossless */
int trithon_mram_roundtrip(const int8_t *trits) {
    uint8_t pk = mram_pack_trits((const trit *)trits);
    trit out[5];
    mram_unpack_trits(pk, out);
    for (int i = 0; i < 5; i++) {
        if (out[i] != (trit)trits[i]) return 0;
    }
    return 1;
}

/** MRAM write/read roundtrip on a small array */
int trithon_mram_write_read(int8_t val) {
    mram_array_t arr;
    mram_init(&arr, 2, 2);
    mram_write_trit(&arr, 0, 0, (trit)val);
    return (int8_t)mram_read_trit(&arr, 0, 0);
}

/** MRAM nominal resistance for MTJ state */
int trithon_mram_nominal_r(int state) {
    return mram_nominal_resistance((mtj_state_t)state);
}

/* ===================================================================== */
/*  8.  T-IPC Module Wrappers                                           */
/* ===================================================================== */

/** T-IPC compress/decompress roundtrip: returns 1 if lossless */
int trithon_tipc_roundtrip(const int8_t *trits, int count) {
    tipc_compressed_t comp;
    if (tipc_compress(&comp, (const trit *)trits, count) < 0) return 0;
    int8_t out[512];
    int dc = tipc_decompress((trit *)out, 512, &comp);
    if (dc != count) return 0;
    for (int i = 0; i < count; i++) {
        if (out[i] != trits[i]) return 0;
    }
    return 1;
}

/** T-IPC guardian compute */
int8_t trithon_tipc_guardian(const int8_t *trits, int count) {
    return (int8_t)tipc_guardian_compute((const trit *)trits, count);
}

/** T-IPC compression ratio ×1000 */
int trithon_tipc_compression_ratio(const int8_t *trits, int count) {
    tipc_compressed_t comp;
    if (tipc_compress(&comp, (const trit *)trits, count) < 0) return 0;
    return tipc_compression_ratio(&comp);
}

/** T-IPC radix guard: returns number of violations */
int trithon_tipc_radix_guard(const uint8_t *data, int len) {
    return tipc_radix_guard(data, len);
}

/* ===================================================================== */
/*  9.  TFS Module Wrappers                                             */
/* ===================================================================== */

/** TFS Huffman encode/decode roundtrip: returns 1 if lossless */
int trithon_tfs_roundtrip(const int8_t *trits, int count) {
    tfs_compressed_block_t comp;
    if (tfs_huffman_encode(&comp, (const trit *)trits, count) < 0) return 0;
    int8_t out[256];
    int dc = tfs_huffman_decode((trit *)out, 256, &comp);
    if (dc != count) return 0;
    for (int i = 0; i < count; i++) {
        if (out[i] != trits[i]) return 0;
    }
    return 1;
}

/** TFS guardian compute */
int8_t trithon_tfs_guardian(const int8_t *trits, int count) {
    return (int8_t)tfs_guardian_compute((const trit *)trits, count);
}

/** TFS density gain ×100 */
int trithon_tfs_density_gain(void) {
    return tfs_density_gain_x100();
}

/** TFS area reduction ×100 */
int trithon_tfs_area_reduction(void) {
    return tfs_area_reduction_x100();
}

/** TFS file write/read roundtrip */
int trithon_tfs_file_roundtrip(const int8_t *trits, int count) {
    tfs_state_t fs;
    tfs_init(&fs);
    tfs_fd_t fd;
    if (tfs_open(&fs, "py_test.t", TFS_MODE_WRITE, &fd) != 0) return 0;
    if (tfs_write(&fs, &fd, (const trit *)trits, count) < 0) return 0;
    tfs_close(&fs, &fd);
    if (tfs_open(&fs, "py_test.t", TFS_MODE_READ, &fd) != 0) return 0;
    int8_t out[512];
    int rlen = tfs_read(&fs, &fd, (trit *)out, 512);
    tfs_close(&fs, &fd);
    if (rlen != count) return 0;
    for (int i = 0; i < count; i++) {
        if (out[i] != trits[i]) return 0;
    }
    return 1;
}
