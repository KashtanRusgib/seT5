/*
 * seT5 Ternary Emulation — 2-bit Packed Structs & Intrinsics
 *
 * Encoding: 00 = -1 (false), 01 = 0 (unknown), 10 = +1 (true), 11 = fault
 * Storage:  trit2_reg32 = 32 trits in uint64_t (2 bits each)
 *           trit2_reg16 = 16 trits in uint32_t
 *
 * Reference: Setun computer (Brusentsov, 1958); seT5 INITIAL_PROJECT_ANSWERS
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

#define TRIT2_FALSE   0x00u  /* 00 = -1 */
#define TRIT2_UNKNOWN 0x01u  /* 01 =  0 */
#define TRIT2_TRUE    0x02u  /* 10 = +1 */
#define TRIT2_FAULT   0x03u  /* 11 = fault (trapped) */

/* ---- Single trit in 2-bit form ---------------------------------------- */

typedef uint8_t trit2;  /* only low 2 bits used */

static inline trit2 trit2_encode(int v) {
    switch (v) {
    case -1: return TRIT2_FALSE;
    case  0: return TRIT2_UNKNOWN;
    case  1: return TRIT2_TRUE;
    default: return TRIT2_FAULT;
    }
}

static inline int trit2_decode(trit2 t) {
    static const int lut[4] = { -1, 0, 1, 0 /* fault->clamp */ };
    return lut[t & 0x03];
}

static inline int trit2_is_fault(trit2 t) {
    return (t & 0x03) == TRIT2_FAULT;
}

/* ---- Scalar Kleene ops on trit2 --------------------------------------- */

static inline trit2 trit2_and(trit2 a, trit2 b) {
    return (a < b) ? a : b;
}

static inline trit2 trit2_or(trit2 a, trit2 b) {
    return (a > b) ? a : b;
}

static inline trit2 trit2_not(trit2 a) {
    static const trit2 lut[4] = { 0x02, 0x01, 0x00, 0x03 };
    return lut[a & 0x03];
}

/* ---- 32-trit SIMD register (64 bits) ---------------------------------- */

typedef struct {
    uint64_t bits;
} trit2_reg32;

#define TRIT2_HI_MASK 0xAAAAAAAAAAAAAAAAULL
#define TRIT2_LO_MASK 0x5555555555555555ULL

static inline void trit2_reg32_set(trit2_reg32 *r, int pos, trit2 val) {
    int shift = pos * 2;
    r->bits = (r->bits & ~((uint64_t)0x03 << shift))
            | ((uint64_t)(val & 0x03) << shift);
}

static inline trit2 trit2_reg32_get(const trit2_reg32 *r, int pos) {
    return (trit2)((r->bits >> (pos * 2)) & 0x03);
}

static inline trit2_reg32 trit2_reg32_splat(trit2 val) {
    trit2_reg32 r;
    uint64_t pair = (uint64_t)(val & 0x03);
    r.bits = pair * 0x5555555555555555ULL;
    return r;
}

/*
 * Kleene AND on 32 trits simultaneously.
 * AND = min(a, b) per 2-bit pair using bit-parallel compare-and-select.
 */
static inline trit2_reg32 trit2_reg32_and(trit2_reg32 a, trit2_reg32 b) {
    trit2_reg32 r;
    uint64_t a_h = (a.bits & TRIT2_HI_MASK) >> 1;
    uint64_t b_h = (b.bits & TRIT2_HI_MASK) >> 1;
    uint64_t a_lo = a.bits & TRIT2_LO_MASK;
    uint64_t b_lo = b.bits & TRIT2_LO_MASK;

    uint64_t lt_hi = ~a_h & b_h & TRIT2_LO_MASK;
    uint64_t eq_hi = ~(a_h ^ b_h) & TRIT2_LO_MASK;
    uint64_t lt_lo = ~a_lo & b_lo & TRIT2_LO_MASK;
    uint64_t lt = lt_hi | (eq_hi & lt_lo);

    uint64_t mask = lt | (lt << 1);
    r.bits = (a.bits & mask) | (b.bits & ~mask);
    return r;
}

static inline trit2_reg32 trit2_reg32_or(trit2_reg32 a, trit2_reg32 b) {
    trit2_reg32 r;
    uint64_t a_h = (a.bits & TRIT2_HI_MASK) >> 1;
    uint64_t b_h = (b.bits & TRIT2_HI_MASK) >> 1;
    uint64_t a_lo = a.bits & TRIT2_LO_MASK;
    uint64_t b_lo = b.bits & TRIT2_LO_MASK;

    uint64_t gt_hi = a_h & ~b_h & TRIT2_LO_MASK;
    uint64_t eq_hi = ~(a_h ^ b_h) & TRIT2_LO_MASK;
    uint64_t gt_lo = a_lo & ~b_lo & TRIT2_LO_MASK;
    uint64_t gt = gt_hi | (eq_hi & gt_lo);
    uint64_t mask = gt | (gt << 1);

    r.bits = (a.bits & mask) | (b.bits & ~mask);
    return r;
}

static inline trit2_reg32 trit2_reg32_not(trit2_reg32 a) {
    trit2_reg32 r;
    uint64_t hi = (a.bits & TRIT2_HI_MASK) >> 1;
    uint64_t lo = (a.bits & TRIT2_LO_MASK) << 1;
    r.bits = hi | lo;
    return r;
}

static inline int trit2_reg32_has_fault(trit2_reg32 r) {
    uint64_t hi = (r.bits & TRIT2_HI_MASK) >> 1;
    uint64_t lo =  r.bits & TRIT2_LO_MASK;
    return (hi & lo) != 0;
}

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

/* ---- 16-trit half register (32 bits) ---------------------------------- */

typedef struct {
    uint32_t bits;
} trit2_reg16;

static inline trit2_reg16 trit2_reg16_and(trit2_reg16 a, trit2_reg16 b) {
    trit2_reg16 r;
    uint32_t a_h = (a.bits & 0xAAAAAAAAu) >> 1;
    uint32_t b_h = (b.bits & 0xAAAAAAAAu) >> 1;
    uint32_t a_lo = a.bits & 0x55555555u;
    uint32_t b_lo = b.bits & 0x55555555u;
    uint32_t lt_hi = ~a_h & b_h & 0x55555555u;
    uint32_t eq_hi = ~(a_h ^ b_h) & 0x55555555u;
    uint32_t lt_lo = ~a_lo & b_lo & 0x55555555u;
    uint32_t lt = lt_hi | (eq_hi & lt_lo);
    uint32_t mask = lt | (lt << 1);
    r.bits = (a.bits & mask) | (b.bits & ~mask);
    return r;
}

#ifdef __cplusplus
}
#endif

#endif /* SET5_TRIT_EMU_H */
