/**
 * @file trit_emu.h
 * @brief seT5 Ternary Emulation — 2-bit Packed Structs & SIMD Intrinsics
 *
 * Efficient binary emulation of balanced ternary logic using 2-bit packed
 * encoding with bit-parallel bulk operations and 4x loop unrolling.
 *
 * Encoding: 00 = -1 (false), 01 = 0 (unknown), 11 = +1 (true), 10 = fault
 * Storage:  trit2_reg32 = 32 trits in uint64_t (2 bits each)
 *           trit2_reg16 = 16 trits in uint32_t
 *
 * Performance target: <0.002s for 1M Kleene AND ops, <15% overhead vs binary
 *
 * Reference: Setun computer (Brusentsov, 1958); seT5 INITIAL_PROJECT_ANSWERS
 *            AFP "Three-Valued Logic" — Kleene lattice meet/join as min/max
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET5_TRIT_EMU_H
#define SET5_TRIT_EMU_H

#include <stdint.h>
#include <string.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ---- 2-bit encoding constants ----------------------------------------- */

/** @brief 2-bit encoding for false (-1) */
#define TRIT2_FALSE   0x00u  /* 00 = -1 */
/** @brief 2-bit encoding for unknown (0) */
#define TRIT2_UNKNOWN 0x01u  /* 01 =  0 */
/** @brief 2-bit encoding for true (+1) */
#define TRIT2_TRUE    0x03u  /* 11 = +1 */
/** @brief 2-bit encoding for fault (trapped) */
#define TRIT2_FAULT   0x02u  /* 10 = fault (trapped) */

/* ---- Single trit in 2-bit form ---------------------------------------- */

/** @brief A single trit stored in 2-bit encoding (only low 2 bits used) */
typedef uint8_t trit2;

/**
 * @brief Encode an integer value as a 2-bit trit.
 * @param v Input value: -1, 0, or +1. Out-of-range produces TRIT2_FAULT.
 * @return 2-bit encoded trit.
 */
static inline trit2 trit2_encode(int v) {
    switch (v) {
    case -1: return TRIT2_FALSE;
    case  0: return TRIT2_UNKNOWN;
    case  1: return TRIT2_TRUE;
    default: return TRIT2_FAULT;
    }
}

/**
 * @brief Decode a 2-bit trit back to integer form.
 * @param t 2-bit encoded trit.
 * @return Integer value: -1, 0, or +1. Fault clamps to 0.
 */
static inline int trit2_decode(trit2 t) {
    static const int lut[4] = { -1, 0, 0 /* fault->clamp */, 1 };
    return lut[t & 0x03];
}

/**
 * @brief Check if a 2-bit trit is a fault value (11).
 * @param t 2-bit encoded trit.
 * @return Non-zero if fault.
 */
static inline int trit2_is_fault(trit2 t) {
    return (t & 0x03) == TRIT2_FAULT;
}

/* ---- Scalar Kleene ops on trit2 --------------------------------------- */

/**
 * @brief Kleene AND on scalar trits: min(a, b).
 * @param a First operand.
 * @param b Second operand.
 * @return Kleene AND result (lattice meet).
 */
static inline trit2 trit2_and(trit2 a, trit2 b) {
    return (a < b) ? a : b;
}

/**
 * @brief Kleene OR on scalar trits: max(a, b).
 * @param a First operand.
 * @param b Second operand.
 * @return Kleene OR result (lattice join).
 */
static inline trit2 trit2_or(trit2 a, trit2 b) {
    return (a > b) ? a : b;
}

/**
 * @brief Kleene NOT on scalar trit: involution.
 * @param a Trit operand.
 * @return F(00)->T(11), T(11)->F(00), U(01)->U(01), fault->fault.
 */
static inline trit2 trit2_not(trit2 a) {
    static const trit2 lut[4] = { 0x03, 0x01, 0x02, 0x00 };
    return lut[a & 0x03];
}

/* ---- 32-trit SIMD register (64 bits) ---------------------------------- */

/**
 * @brief 32 trits packed into a single 64-bit word (2 bits each).
 *
 * Primary SIMD unit for ternary emulation. Each operation processes
 * 32 Kleene logic ops in parallel via bitwise manipulation.
 */
typedef struct {
    uint64_t bits;  /**< 32 trits x 2 bits = 64 bits */
} trit2_reg32;

/** @brief Bitmask selecting high bits of each 2-bit pair */
#define TRIT2_HI_MASK 0xAAAAAAAAAAAAAAAAULL
/** @brief Bitmask selecting low bits of each 2-bit pair */
#define TRIT2_LO_MASK 0x5555555555555555ULL

/**
 * @brief Set a trit at position [0..31] in a 32-trit register.
 * @param r   Pointer to register.
 * @param pos Trit index (0 = LSB pair).
 * @param val 2-bit trit value.
 */
static inline void trit2_reg32_set(trit2_reg32 *r, int pos, trit2 val) {
    int shift = pos * 2;
    r->bits = (r->bits & ~((uint64_t)0x03 << shift))
            | ((uint64_t)(val & 0x03) << shift);
}

/**
 * @brief Get a trit at position [0..31] from a 32-trit register.
 * @param r   Pointer to register.
 * @param pos Trit index (0 = LSB pair).
 * @return 2-bit trit value.
 */
static inline trit2 trit2_reg32_get(const trit2_reg32 *r, int pos) {
    return (trit2)((r->bits >> (pos * 2)) & 0x03);
}

/**
 * @brief Fill all 32 slots with the same trit value.
 * @param val 2-bit trit value to broadcast.
 * @return Register with all 32 trits set to val.
 */
static inline trit2_reg32 trit2_reg32_splat(trit2 val) {
    trit2_reg32 r;
    uint64_t pair = (uint64_t)(val & 0x03);
    r.bits = pair * TRIT2_LO_MASK;
    return r;
}

/**
 * @brief Kleene AND on 32 trits — single bitwise AND instruction.
 *
 * With encoding F=00 U=01 T=11, Kleene meet (min) equals bitwise &.
 * Proof: & maps (F,x)->F, (U,T)->(01&11)=01=U, (T,T)->T. QED
 *
 * @param a First 32-trit register.
 * @param b Second 32-trit register.
 * @return Pair-wise Kleene AND of a and b.
 */
static inline trit2_reg32 trit2_reg32_and(trit2_reg32 a, trit2_reg32 b) {
    trit2_reg32 r;
    r.bits = a.bits & b.bits;
    return r;
}

/**
 * @brief Kleene OR on 32 trits — single bitwise OR instruction.
 *
 * With encoding F=00 U=01 T=11, Kleene join (max) equals bitwise |.
 * Proof: | maps (T,x)->T, (U,F)->(01|00)=01=U, (F,F)->F. QED
 *
 * @param a First 32-trit register.
 * @param b Second 32-trit register.
 * @return Pair-wise Kleene OR of a and b.
 */
static inline trit2_reg32 trit2_reg32_or(trit2_reg32 a, trit2_reg32 b) {
    trit2_reg32 r;
    r.bits = a.bits | b.bits;
    return r;
}

/**
 * @brief Kleene NOT on 32 trits: F(00)<->T(11), U(01) fixed-point.
 *
 * NOT(00)=11, NOT(01)=01, NOT(11)=00, NOT(10)=10 (fault preserved).
 * Derivation: XOR each pair with 11 iff hi==lo (XNOR-gated flip).
 *
 * @param a 32-trit register.
 * @return Pair-wise Kleene NOT (involution).
 */
static inline trit2_reg32 trit2_reg32_not(trit2_reg32 a) {
    trit2_reg32 r;
    uint64_t hi = (a.bits >> 1) & TRIT2_LO_MASK;
    uint64_t lo =  a.bits       & TRIT2_LO_MASK;
    uint64_t eq = ~(hi ^ lo) & TRIT2_LO_MASK;  /* 1 where hi==lo */
    uint64_t mask = eq | (eq << 1);              /* expand to pair  */
    r.bits = a.bits ^ mask;
    return r;
}

/**
 * @brief Detect any fault trits (encoding 10) in a 32-trit register.
 * @param r 32-trit register.
 * @return Non-zero if any trit has the fault encoding.
 */
static inline int trit2_reg32_has_fault(trit2_reg32 r) {
    uint64_t hi = (r.bits >> 1) & TRIT2_LO_MASK;
    uint64_t lo =  r.bits       & TRIT2_LO_MASK;
    return (hi & ~lo) != 0;    /* 10 pattern = fault */
}

/**
 * @brief Count trits of each value in a 32-trit register.
 * @param r          Register to census.
 * @param[out] n_false   Count of F trits (may be NULL).
 * @param[out] n_unknown Count of U trits (may be NULL).
 * @param[out] n_true    Count of T trits (may be NULL).
 * @param[out] n_fault   Count of fault trits (may be NULL).
 */
static inline void trit2_reg32_census(trit2_reg32 r,
                                      int *n_false, int *n_unknown,
                                      int *n_true, int *n_fault) {
    int f = 0, u = 0, t = 0, x = 0;
    for (int i = 0; i < 32; i++) {
        switch (trit2_reg32_get(&r, i)) {
        case TRIT2_FALSE:   f++; break;
        case TRIT2_UNKNOWN: u++; break;
        case TRIT2_TRUE:    t++; break;
        default:            x++; break;
        }
    }
    if (n_false)   *n_false   = f;
    if (n_unknown) *n_unknown = u;
    if (n_true)    *n_true    = t;
    if (n_fault)   *n_fault   = x;
}

/* ---- Bulk operations with 4x loop unrolling --------------------------- */

/**
 * @brief Bulk Kleene AND over arrays of 32-trit registers (4x unrolled).
 *
 * Processes n registers with 4x unrolling for instruction-level parallelism.
 * Each iteration handles 128 trits (4 x 32). Designed for seL4 fastpath
 * capability batch checks.
 *
 * @param[out] dst Destination array (n elements).
 * @param[in]  a   First source array (n elements).
 * @param[in]  b   Second source array (n elements).
 * @param      n   Number of registers to process.
 */
static inline void trit2_reg32_and_bulk(trit2_reg32 *dst,
                                        const trit2_reg32 *a,
                                        const trit2_reg32 *b,
                                        int n) {
    int i = 0;
    for (; i + 3 < n; i += 4) {
        dst[i + 0] = trit2_reg32_and(a[i + 0], b[i + 0]);
        dst[i + 1] = trit2_reg32_and(a[i + 1], b[i + 1]);
        dst[i + 2] = trit2_reg32_and(a[i + 2], b[i + 2]);
        dst[i + 3] = trit2_reg32_and(a[i + 3], b[i + 3]);
    }
    for (; i < n; i++) {
        dst[i] = trit2_reg32_and(a[i], b[i]);
    }
}

/**
 * @brief Bulk Kleene OR over arrays of 32-trit registers (4x unrolled).
 * @param[out] dst Destination array.
 * @param[in]  a   First source array.
 * @param[in]  b   Second source array.
 * @param      n   Number of registers.
 */
static inline void trit2_reg32_or_bulk(trit2_reg32 *dst,
                                       const trit2_reg32 *a,
                                       const trit2_reg32 *b,
                                       int n) {
    int i = 0;
    for (; i + 3 < n; i += 4) {
        dst[i + 0] = trit2_reg32_or(a[i + 0], b[i + 0]);
        dst[i + 1] = trit2_reg32_or(a[i + 1], b[i + 1]);
        dst[i + 2] = trit2_reg32_or(a[i + 2], b[i + 2]);
        dst[i + 3] = trit2_reg32_or(a[i + 3], b[i + 3]);
    }
    for (; i < n; i++) {
        dst[i] = trit2_reg32_or(a[i], b[i]);
    }
}

/**
 * @brief Bulk Kleene NOT over arrays of 32-trit registers (4x unrolled).
 * @param[out] dst Destination array.
 * @param[in]  a   Source array.
 * @param      n   Number of registers.
 */
static inline void trit2_reg32_not_bulk(trit2_reg32 *dst,
                                        const trit2_reg32 *a,
                                        int n) {
    int i = 0;
    for (; i + 3 < n; i += 4) {
        dst[i + 0] = trit2_reg32_not(a[i + 0]);
        dst[i + 1] = trit2_reg32_not(a[i + 1]);
        dst[i + 2] = trit2_reg32_not(a[i + 2]);
        dst[i + 3] = trit2_reg32_not(a[i + 3]);
    }
    for (; i < n; i++) {
        dst[i] = trit2_reg32_not(a[i]);
    }
}

/* ---- Zero-trit sparsity (N:M structured, TENET-inspired) -------------- */

/**
 * @brief Count zero (Unknown) trits in a 32-trit register for sparsity.
 *
 * Returns the number of 0-trits (Unknown, encoded 01).  Used by DOT_TRIT
 * to skip zero-weight positions and by the register file to detect sparse
 * values for N:M structured sparsity (TENET-style).  A register with
 * >50% zero density qualifies for sparse execution.
 *
 * @param r  32-trit register to analyze.
 * @return   Number of zero/Unknown trits (0..32).
 */
static inline int trit2_reg32_zero_count(trit2_reg32 r) {
    int count = 0;
    for (int i = 0; i < 32; i++) {
        if (trit2_reg32_get(&r, i) == TRIT2_UNKNOWN)
            count++;
    }
    return count;
}

/**
 * @brief Check if a register is sparse (>50% zero trits).
 * @param r  32-trit register.
 * @return   1 if sparse, 0 otherwise.
 */
static inline int trit2_reg32_is_sparse(trit2_reg32 r) {
    return trit2_reg32_zero_count(r) > 16;
}

/* ---- 16-trit half register (32 bits) ---------------------------------- */

/** @brief 16 trits packed into a 32-bit word (for embedded targets) */
typedef struct {
    uint32_t bits;  /**< 16 trits x 2 bits = 32 bits */
} trit2_reg16;

/**
 * @brief Kleene AND on 16 trits (32-bit version for embedded targets).
 * @param a First 16-trit register.
 * @param b Second 16-trit register.
 * @return Pair-wise Kleene AND.
 */
static inline trit2_reg16 trit2_reg16_and(trit2_reg16 a, trit2_reg16 b) {
    trit2_reg16 r;
    uint32_t a_hi = a.bits & 0xAAAAAAAAu;
    uint32_t a_lo = a.bits & 0x55555555u;
    uint32_t b_hi = b.bits & 0xAAAAAAAAu;
    uint32_t b_lo = b.bits & 0x55555555u;
    uint32_t r_hi = a_hi | b_hi;
    uint32_t r_lo = a_lo & b_lo & ~(r_hi >> 1);
    r.bits = r_hi | r_lo;
    return r;
}

/**
 * @brief Kleene OR on 16 trits (32-bit version for embedded targets).
 * @param a First 16-trit register.
 * @param b Second 16-trit register.
 * @return Pair-wise Kleene OR.
 */
static inline trit2_reg16 trit2_reg16_or(trit2_reg16 a, trit2_reg16 b) {
    trit2_reg16 r;
    uint32_t a_hi = a.bits & 0xAAAAAAAAu;
    uint32_t a_lo = a.bits & 0x55555555u;
    uint32_t b_hi = b.bits & 0xAAAAAAAAu;
    uint32_t b_lo = b.bits & 0x55555555u;
    uint32_t r_lo = a_lo | b_lo;
    uint32_t r_hi = a_hi & b_hi & ~(r_lo << 1);
    r.bits = r_hi | r_lo;
    return r;
}

/**
 * @brief Kleene NOT on 16 trits — swap hi/lo bits in each pair.
 * @param a 16-trit register to negate.
 * @return Bitwise trit negation.
 */
static inline trit2_reg16 trit2_reg16_not(trit2_reg16 a) {
    trit2_reg16 r;
    uint32_t hi = (a.bits & 0xAAAAAAAAu) >> 1;
    uint32_t lo = (a.bits & 0x55555555u) << 1;
    r.bits = hi | lo;
    return r;
}

/**
 * @brief Splat a single trit2 value across all 16 positions.
 * @param v 2-bit trit value to broadcast.
 * @return 16-trit register with v in every position.
 */
static inline trit2_reg16 trit2_reg16_splat(trit2 v) {
    trit2_reg16 r;
    uint32_t pair = (uint32_t)(v & 0x03);
    uint32_t spread = 0;
    for (int i = 0; i < 16; i++)
        spread |= (pair << (i * 2));
    r.bits = spread;
    return r;
}

#ifdef __cplusplus
}
#endif

#endif /* SET5_TRIT_EMU_H */
