/**
 * @file trit.h
 * @brief seT6 Ternary Type — Balanced Ternary with Kleene Logic
 *
 * Core trit type using scalar int8_t representation with values
 * {-1 (False), 0 (Unknown), +1 (True)}.
 *
 * Provides:
 *   - Kleene AND (meet), OR (join), NOT (involution)
 *   - IMPLIES, EQUIV derived operations
 *   - Predicates: trit_is_definite(), trit_to_bool_safe()
 *   - 2-bit pack/unpack for SIMD (T=11 encoding)
 *   - 32-trit packed AND/OR on uint64_t
 *
 * Encoding (2-bit packed):
 *   00 = False (-1), 01 = Unknown (0), 11 = True (+1), 10 = Fault
 *
 * @see trit_emu.h for full SIMD emulation layer
 * @see TritKleene.thy for formal proofs of these operations
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_TRIT_H
#define SET6_TRIT_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* --- Representation ---------------------------------------------------- */

typedef int8_t trit; /* stored as -1, 0, +1 */

#define TRIT_FALSE   ((trit)-1)
#define TRIT_UNKNOWN ((trit) 0)
#define TRIT_TRUE    ((trit)+1)

/* Literal for unknown: the '?' token maps here */
#define __unknown TRIT_UNKNOWN

/* --- 2-bit packed encoding (for registers / SIMD) ---------------------- */

typedef uint8_t trit_packed; /* 0b10=-1, 0b00=0, 0b01=+1, 0b11=fault */

static inline trit_packed trit_pack(trit v) {
    /* Map: -1 -> 0b10, 0 -> 0b00, +1 -> 0b01 */
    static const trit_packed lut[3] = { 0x02, 0x00, 0x01 }; /* [-1,0,+1] */
    return lut[(int)(v + 1)];
}

static inline trit trit_unpack(trit_packed p) {
    /* 0b00->0, 0b01->+1, 0b10->-1, 0b11->fault(clamp to 0) */
    static const trit lut[4] = { 0, 1, -1, 0 };
    return lut[p & 0x03];
}

/* --- Kleene Logic Operators -------------------------------------------- */

/* AND: min(a, b) — unknown absorbs false, propagates over true */
static inline trit trit_and(trit a, trit b) {
    return (a < b) ? a : b;
}

/* OR: max(a, b) — unknown absorbs true, propagates over false */
static inline trit trit_or(trit a, trit b) {
    return (a > b) ? a : b;
}

/* NOT: negation — -a */
static inline trit trit_not(trit a) {
    return (trit)(-a);
}

/* IMPLIES: Kleene implication — max(-a, b) */
static inline trit trit_implies(trit a, trit b) {
    return trit_or(trit_not(a), b);
}

/* EQUIV: a iff b — trit_and(trit_implies(a,b), trit_implies(b,a)) */
static inline trit trit_equiv(trit a, trit b) {
    return trit_and(trit_implies(a, b), trit_implies(b, a));
}

/* --- Predicates (collapse to binary for branching) --------------------- */

/* Definite: returns 1 iff value is not unknown */
static inline int trit_is_definite(trit v) {
    return v != TRIT_UNKNOWN;
}

/* Safe-to-true: conservative collapse — unknown becomes false */
static inline int trit_to_bool_safe(trit v) {
    return v == TRIT_TRUE;
}

/* --- SIMD bulk operations (32 trits in a uint64_t) --------------------- */

/*
 * Pack 32 trits into a 64-bit word (2 bits each, LSB-first).
 * Kleene AND on packed words: per-pair min via bitwise ops.
 *
 * Encoding truth table for AND (2-bit pairs):
 *   00 & xx = 00  (unknown absorbs when neither is false)
 *   10 & xx = 10  (false dominates)
 *   01 & 01 = 01  (true & true)
 *   01 & 00 = 00  (true & unknown = unknown)
 *
 * Implementation: treat high-bit as "negative" flag, low-bit as "positive".
 *   result_hi = a_hi | b_hi          (either false -> false)
 *   result_lo = a_lo & b_lo & ~result_hi  (both true, not false)
 */
static inline uint64_t trit_and_packed64(uint64_t a, uint64_t b) {
    uint64_t a_hi = a & 0xAAAAAAAAAAAAAAAAULL;
    uint64_t a_lo = a & 0x5555555555555555ULL;
    uint64_t b_hi = b & 0xAAAAAAAAAAAAAAAAULL;
    uint64_t b_lo = b & 0x5555555555555555ULL;
    uint64_t r_hi = a_hi | b_hi;
    uint64_t r_lo = a_lo & b_lo & ~(r_hi >> 1);
    return r_hi | r_lo;
}

static inline uint64_t trit_or_packed64(uint64_t a, uint64_t b) {
    uint64_t a_hi = a & 0xAAAAAAAAAAAAAAAAULL;
    uint64_t a_lo = a & 0x5555555555555555ULL;
    uint64_t b_hi = b & 0xAAAAAAAAAAAAAAAAULL;
    uint64_t b_lo = b & 0x5555555555555555ULL;
    uint64_t r_lo = a_lo | b_lo;
    uint64_t r_hi = a_hi & b_hi & ~(r_lo << 1);
    return r_hi | r_lo;
}

static inline uint64_t trit_not_packed64(uint64_t a) {
    /* Swap hi and lo bits in each pair */
    uint64_t hi = (a & 0xAAAAAAAAAAAAAAAAULL) >> 1;
    uint64_t lo = (a & 0x5555555555555555ULL) << 1;
    return hi | lo;
}

#ifdef __cplusplus
}
#endif

#endif /* SET6_TRIT_H */
