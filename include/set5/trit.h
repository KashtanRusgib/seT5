/**
 * @file trit.h
 * @brief seT5 Ternary Type — Balanced Ternary with Kleene Logic
 *
 * Core trit type using scalar int8_t representation with values
 * {-1 (False), 0 (Unknown), +1 (True)}.
 *
 * Provides:
 *   - Kleene AND (meet), OR (join), NOT (involution)
 *   - IMPLIES, EQUIV derived operations
 *   - Predicates: trit_is_definite(), trit_to_bool_safe()
 *   - 2-bit pack/unpack for SIMD (hi=neg, lo=pos encoding)
 *   - 32-trit packed AND/OR on uint64_t
 *
 * Encoding (2-bit packed — matches SIMD hi/lo convention):
 *   10 = False (-1), 00 = Unknown (0), 01 = True (+1), 11 = Fault
 *
 * @see trit_emu.h for full SIMD emulation layer
 * @see TritKleene.thy for formal proofs of these operations
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET5_TRIT_H
#define SET5_TRIT_H

#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

/* --- T-026: TRIT_RANGE_CHECK macro ------------------------------------- */
#define TRIT_RANGE_CHECK(v) ((v) >= -1 && (v) <= 1)

    /* --- Representation ---------------------------------------------------- */

    typedef int8_t trit; /* stored as -1, 0, +1 */

#define TRIT_FALSE ((trit) - 1)
#define TRIT_UNKNOWN ((trit)0)
#define TRIT_TRUE ((trit) + 1)

/* Literal for unknown: the '?' token maps here */
#define __unknown TRIT_UNKNOWN

    /* --- 2-bit packed encoding (for registers / SIMD) ---------------------- */

    typedef uint8_t trit_packed; /* 0b10=-1, 0b00=0, 0b01=+1, 0b11=fault */

    static inline trit_packed trit_pack(trit v)
    {
        /* Map: -1 → 0b10, 0 → 0b00, +1 → 0b01
         * Old impl (v & 0x03) mapped -1 → 0b11 (fault slot!) — WRONG.
         * This conditional matches the SIMD hi=neg/lo=pos convention. */
        if (v < 0)
            return 0x02; /* FALSE  → 0b10 (hi=1, lo=0) */
        if (v > 0)
            return 0x01; /* TRUE   → 0b01 (hi=0, lo=1) */
        return 0x00;     /* UNKNOWN → 0b00             */
    }

    static inline trit trit_unpack(trit_packed p)
    {
        /* 0b00->0, 0b01->+1, 0b10->-1, 0b11->fault(clamp to 0) */
        static const trit lut[4] = {0, 1, -1, 0};
        return lut[p & 0x03];
    }

    /* --- Kleene Logic Operators -------------------------------------------- */

    /* AND: min(a, b) — unknown absorbs false, propagates over true */
    static inline trit trit_and(trit a, trit b)
    {
        return (a < b) ? a : b;
    }

    /* OR: max(a, b) — unknown absorbs true, propagates over false */
    static inline trit trit_or(trit a, trit b)
    {
        return (a > b) ? a : b;
    }

    /* NOT: negation — -a */
    static inline trit trit_not(trit a)
    {
        return (trit)(-a);
    }

    /* IMPLIES: Kleene implication — max(-a, b) */
    static inline trit trit_implies(trit a, trit b)
    {
        return trit_or(trit_not(a), b);
    }

    /* EQUIV: a iff b — trit_and(trit_implies(a,b), trit_implies(b,a)) */
    static inline trit trit_equiv(trit a, trit b)
    {
        return trit_and(trit_implies(a, b), trit_implies(b, a));
    }

    /* --- Predicates (collapse to binary for branching) --------------------- */

    /* Definite: returns 1 iff value is not unknown */
    static inline int trit_is_definite(trit v)
    {
        return v != TRIT_UNKNOWN;
    }

    /* Safe-to-true: conservative collapse — unknown becomes false */
    static inline int trit_to_bool_safe(trit v)
    {
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
    static inline uint64_t trit_and_packed64(uint64_t a, uint64_t b)
    {
        uint64_t a_hi = a & 0xAAAAAAAAAAAAAAAAULL;
        uint64_t a_lo = a & 0x5555555555555555ULL;
        uint64_t b_hi = b & 0xAAAAAAAAAAAAAAAAULL;
        uint64_t b_lo = b & 0x5555555555555555ULL;
        uint64_t r_hi = a_hi | b_hi;
        uint64_t r_lo = a_lo & b_lo & ~(r_hi >> 1);
        return r_hi | r_lo;
    }

    static inline uint64_t trit_or_packed64(uint64_t a, uint64_t b)
    {
        uint64_t a_hi = a & 0xAAAAAAAAAAAAAAAAULL;
        uint64_t a_lo = a & 0x5555555555555555ULL;
        uint64_t b_hi = b & 0xAAAAAAAAAAAAAAAAULL;
        uint64_t b_lo = b & 0x5555555555555555ULL;
        uint64_t r_lo = a_lo | b_lo;
        uint64_t r_hi = a_hi & b_hi & ~(r_lo << 1);
        return r_hi | r_lo;
    }

    static inline uint64_t trit_not_packed64(uint64_t a)
    {
        /* Swap hi and lo bits in each pair */
        uint64_t hi = (a & 0xAAAAAAAAAAAAAAAAULL) >> 1;
        uint64_t lo = (a & 0x5555555555555555ULL) << 1;
        return hi | lo;
    }

    /* --- T-SEC: Packed64 Fault Detection and Hardening -------------------- */
    /*
     * Security finding (Suite 91 / test_6304):
     *   trit_or_packed64(fault=0b11, false=0b10) = true=0b01
     *   Fault lo-bit == 1 is indistinguishable from TRUE lo-bit in the OR formula.
     *   All three hardened ops below sanitize fault slots (0b11 → 0b00=UNKNOWN)
     *   before applying the core Kleene formula, ensuring fault cannot masquerade.
     *
     * Proof: see proof/PackedFaultSemantics.thy
     */

    /*
     * has_fault_packed64 — detect any fault (0b11) slot in a packed word.
     * A slot is faulty iff its hi-bit AND its lo-bit are both set.
     * Returns non-zero (true) if any fault slot is present.
     * Cost: 3 bitwise ops, O(1).
     */
    static inline int has_fault_packed64(uint64_t w)
    {
        uint64_t hi = (w >> 1) & 0x5555555555555555ULL; /* hi-bits shifted to lo lane */
        uint64_t lo = w & 0x5555555555555555ULL;        /* lo-bits                      */
        return (hi & lo) != 0;
    }

    /*
     * trit_sanitize_packed64 — replace every fault (0b11) slot with UNKNOWN (0b00).
     * All valid {0b00, 0b01, 0b10} slots are preserved exactly.
     * Cost: 5 bitwise ops, O(1).
     */
    static inline uint64_t trit_sanitize_packed64(uint64_t w)
    {
        uint64_t lo = w & 0x5555555555555555ULL;
        uint64_t hi = (w >> 1) & 0x5555555555555555ULL;
        uint64_t fault_pos = lo & hi;                       /* 1 at positions [0,2,4,...] of each fault slot */
        uint64_t fault_full = fault_pos | (fault_pos << 1); /* expand to cover both bits of each pair */
        return w & ~fault_full;                             /* zero fault slots → 0b00 = UNKNOWN */
    }

    /*
     * trit_or_packed64_hardened — sanitizing OR.
     * Sanitizes both inputs (fault→UNKNOWN) before applying Kleene OR.
     * For valid inputs behaves identically to trit_or_packed64.
     * For fault inputs: fault is treated as UNKNOWN (conservative over-approx).
     */
    static inline uint64_t trit_or_packed64_hardened(uint64_t a, uint64_t b)
    {
        return trit_or_packed64(trit_sanitize_packed64(a),
                                trit_sanitize_packed64(b));
    }

    /*
     * trit_and_packed64_hardened — sanitizing AND.
     */
    static inline uint64_t trit_and_packed64_hardened(uint64_t a, uint64_t b)
    {
        return trit_and_packed64(trit_sanitize_packed64(a),
                                 trit_sanitize_packed64(b));
    }

    /*
     * trit_not_packed64_hardened — sanitizing NOT.
     */
    static inline uint64_t trit_not_packed64_hardened(uint64_t a)
    {
        return trit_not_packed64(trit_sanitize_packed64(a));
    }

/*
 * TRIT_PACKED_VALID(w) — evaluates to 1 iff packed word contains no fault slots.
 * Suitable for assertions and debug guards on security-critical paths.
 */
#define TRIT_PACKED_VALID(w) (!has_fault_packed64(w))

    /* --- T-026: Compile-time type size validation -------------------------- */

    _Static_assert(sizeof(trit_packed) == 1, "trit_packed must be 1 byte");
    _Static_assert(sizeof(trit) == 1, "trit must be 1 byte");

/* --- T-026: Runtime Kleene Truth Table Validation ---------------------- */

/*
 * TRIT_RUNTIME_VALIDATE() — call once at startup to verify all 9 AND/OR
 * entries plus 3 NOT entries match Kleene's strong 3-valued logic.
 * Returns 0 on success, -1 on failure.
 */
#define TRIT_RUNTIME_VALIDATE() (                                     \
    (trit_and(TRIT_FALSE, TRIT_FALSE) == TRIT_FALSE) &&               \
            (trit_and(TRIT_FALSE, TRIT_UNKNOWN) == TRIT_FALSE) &&     \
            (trit_and(TRIT_FALSE, TRIT_TRUE) == TRIT_FALSE) &&        \
            (trit_and(TRIT_UNKNOWN, TRIT_FALSE) == TRIT_FALSE) &&     \
            (trit_and(TRIT_UNKNOWN, TRIT_UNKNOWN) == TRIT_UNKNOWN) && \
            (trit_and(TRIT_UNKNOWN, TRIT_TRUE) == TRIT_UNKNOWN) &&    \
            (trit_and(TRIT_TRUE, TRIT_FALSE) == TRIT_FALSE) &&        \
            (trit_and(TRIT_TRUE, TRIT_UNKNOWN) == TRIT_UNKNOWN) &&    \
            (trit_and(TRIT_TRUE, TRIT_TRUE) == TRIT_TRUE) &&          \
            (trit_or(TRIT_FALSE, TRIT_FALSE) == TRIT_FALSE) &&        \
            (trit_or(TRIT_FALSE, TRIT_UNKNOWN) == TRIT_UNKNOWN) &&    \
            (trit_or(TRIT_FALSE, TRIT_TRUE) == TRIT_TRUE) &&          \
            (trit_or(TRIT_UNKNOWN, TRIT_FALSE) == TRIT_UNKNOWN) &&    \
            (trit_or(TRIT_UNKNOWN, TRIT_UNKNOWN) == TRIT_UNKNOWN) &&  \
            (trit_or(TRIT_UNKNOWN, TRIT_TRUE) == TRIT_TRUE) &&        \
            (trit_or(TRIT_TRUE, TRIT_FALSE) == TRIT_TRUE) &&          \
            (trit_or(TRIT_TRUE, TRIT_UNKNOWN) == TRIT_TRUE) &&        \
            (trit_or(TRIT_TRUE, TRIT_TRUE) == TRIT_TRUE) &&           \
            (trit_not(TRIT_FALSE) == TRIT_TRUE) &&                    \
            (trit_not(TRIT_UNKNOWN) == TRIT_UNKNOWN) &&               \
            (trit_not(TRIT_TRUE) == TRIT_FALSE)                       \
        ? 0                                                           \
        : -1)

/* --- T-027: Heptavintimal (Base-27) Gate Aliases (Bos 2024) ----------- */

/*
 * Heptavintimal indices are 1-4 character strings drawn from the set
 * {0-9,A-Z} in base-27, uniquely labelling all 19683 diadic ternary functions.
 * These aliases map common gates onto seT5 trit primitives.
 * Diadic: SUM(7PB)=sum, MIN(PC0)=AND, MAX(ZRP)=OR, MLE(H51)=le, CONS(RDC)=carry
 * Monadic: NTI(2)=NOT, BUF(K)=id, INC(7)=+1, DEC(B)=-1, PTI(8)=pos, STI(5)=sign
 */
#define TRIT_GATE_SUM(a, b)     ((trit)(((int)(a)+(int)(b)>1)?1:((int)(a)+(int)(b)<-1)?-1:(int)((a)+(b))))
#define TRIT_GATE_MIN(a, b)   trit_and((a),(b))
#define TRIT_GATE_MAX(a, b)   trit_or((a),(b))
#define TRIT_GATE_MLE(a, b)   ((trit)((a)<=(b)?1:-1))
#define TRIT_GATE_CONS(a, b)  ((trit)(((a)==(b))?(a):TRIT_UNKNOWN))
#define TRIT_GATE_NTI(a)      trit_not((a))
#define TRIT_GATE_BUF(a)      (a)
#define TRIT_GATE_INC(a)      ((trit)(((int)(a)+1>1)?1:(int)(a)+1))
#define TRIT_GATE_DEC(a)      ((trit)(((int)(a)-1<-1)?-1:(int)(a)-1))
#define TRIT_GATE_PTI(a)      ((trit)((a)==TRIT_TRUE?1:-1))
#define TRIT_GATE_STI(a)      ((trit)((a)>0?1:(a)<0?-1:0))
#define TRIT_GATE_MTI(a)      ((trit)((a)==TRIT_UNKNOWN?1:-1))

#ifdef __cplusplus
}
#endif

#endif /* SET5_TRIT_H */