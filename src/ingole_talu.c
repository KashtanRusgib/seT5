/**
 * @file ingole_talu.c
 * @brief ALU Implementation for WO2016199157A1 Ternary ALU (TALU)
 *
 * Software-emulated implementations of every circuit described in
 * patent WO2016199157A1:
 *
 *   - TNOT, CWC, CCWC unary gates          (4 TG each)
 *   - ADD_1_CARRY LST injector              (4 TG)
 *   - TAND, TNAND, TOR, TNOR binary gates  (8 TG each)
 *   - XTOR exclusive-or                     (14 TG)
 *   - COMPARATOR 3-state compare            (10 TG)
 *   - S1 half-adder, S2 full-adder, C2 carry (6-16 TG)
 *   - 2×9 OPCODE decoder                   (48 TG)
 *   - Full TALU stage and word-level execution
 *
 * All functions accept and return seT5 balanced ternary {-1, 0, +1}.
 * Internal computation uses unbalanced {0, 1, 2} matching the patent.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/ingole_talu.h"
#include <string.h>

/* ===================================================================== */
/* Internal: unbalanced ternary helpers                                  */
/* ===================================================================== */

/** Convert balanced → unbalanced */
static inline int ub(trit v) { return (int)v + 1; }

/** Convert unbalanced → balanced */
static inline trit bt(int v) { return (trit)(v - 1); }

/** Clamp unbalanced to {0, 1, 2} */
static inline int clamp3(int v)
{
    if (v < 0) return 0;
    if (v > 2) return 2;
    return v;
}

/* ===================================================================== */
/* Single-Trit Unary Operations                                          */
/* ===================================================================== */

trit ig_alu_tnot(trit val)
{
    /* TNOT truth table (unbalanced): {0→2, 1→1, 2→0} = (2 - x) */
    int u = ub(val);
    return bt(2 - u);
}

trit ig_alu_cwc(trit val)
{
    /* CWC truth table (unbalanced): {0→0, 1→2, 2→1} */
    static const int lut[3] = {0, 2, 1};
    return bt(lut[ub(val)]);
}

trit ig_alu_ccwc(trit val)
{
    /* CCWC truth table (unbalanced): {0→1, 1→0, 2→2} */
    static const int lut[3] = {1, 0, 2};
    return bt(lut[ub(val)]);
}

void ig_alu_add1carry(trit val, trit *sum, trit *carry)
{
    /* ADD_1_CARRY (unbalanced): (x+1) mod 3, carry = (x+1)/3 */
    int u = ub(val);
    int s = (u + 1) % 3;
    int c = (u + 1) / 3;
    *sum   = bt(s);
    *carry = bt(c);
}

/* ===================================================================== */
/* Two-Trit Binary Operations                                            */
/* ===================================================================== */

trit ig_alu_tand(trit a, trit b)
{
    /* TAND = min(A, B) in unbalanced */
    int ua = ub(a), ub_val = ub(b);
    return bt(ua < ub_val ? ua : ub_val);
}

trit ig_alu_tnand(trit a, trit b)
{
    return ig_alu_tnot(ig_alu_tand(a, b));
}

trit ig_alu_tor(trit a, trit b)
{
    /* TOR = max(A, B) in unbalanced */
    int ua = ub(a), ub_val = ub(b);
    return bt(ua > ub_val ? ua : ub_val);
}

trit ig_alu_tnor(trit a, trit b)
{
    return ig_alu_tnot(ig_alu_tor(a, b));
}

trit ig_alu_xtor(trit a, trit b)
{
    /* XTOR = (A + B) mod 3 in unbalanced */
    int ua = ub(a), ub_val = ub(b);
    return bt((ua + ub_val) % 3);
}

trit ig_alu_comparator(trit a, trit b)
{
    /* Comparator (unbalanced): 0=equal, 1=A>B, 2=A<B */
    int ua = ub(a), ub_val = ub(b);
    int result;
    if (ua == ub_val)     result = 0;  /* equal */
    else if (ua > ub_val) result = 1;  /* A > B */
    else                  result = 2;  /* A < B */
    return bt(result);
}

/* ===================================================================== */
/* Arithmetic                                                            */
/* ===================================================================== */

void ig_alu_half_add(trit a, trit b, trit *sum, trit *carry)
{
    /* S1 = (A + B) mod 3,  C1 = (A + B) / 3  — unbalanced */
    int ua = ub(a), ub_val = ub(b);
    int total = ua + ub_val;
    *sum   = bt(total % 3);
    *carry = bt(total / 3);
}

void ig_alu_full_add(trit a, trit b, trit cin, trit *sum, trit *carry)
{
    /* S2 = (A + B + Cin) mod 3,  C2 = max(C1_ab, C1_s1_cin) */
    int ua = ub(a), ub_val = ub(b), uc = ub(cin);

    /* Half-add A+B */
    int ab = ua + ub_val;
    int s1 = ab % 3;
    int c1_ab = ab / 3;

    /* Half-add S1+Cin */
    int sc = s1 + uc;
    int s2 = sc % 3;
    int c1_sc = sc / 3;

    /* C2 = max(c1_ab, c1_sc) — TOR of carry chains */
    int c2 = c1_ab > c1_sc ? c1_ab : c1_sc;

    *sum   = bt(s2);
    *carry = bt(c2);
}

/* ===================================================================== */
/* Word-Level TALU Execution                                             */
/* ===================================================================== */

/**
 * Internal: compute 3's complement of a word (TNOT each trit, plus 1).
 * Used for subtraction: A - B = A + TNOT(B) + 1
 */
static void threes_complement(const trit *src, trit *dst, int width)
{
    for (int i = 0; i < width; i++) {
        dst[i] = ig_alu_tnot(src[i]);
    }
}

/**
 * Internal: even parity chain — fold XOR (XTOR) across all trits.
 */
static trit parity_chain(const trit *word, int width)
{
    trit p = TRIT_FALSE;  /* Start at 0 in unbalanced (balanced -1 → unbalanced 0) */
    /* Actually start with bt(0) = -1.  We want unbalanced 0 start = bt(0) = -1  */
    /* Hmm, parity starting point: ig_alu_xtor folds (ub(p) + ub(w[i])) mod 3.
       Starting with ub(p)=0 means (0 + ub(w[0])) mod 3 = ub(w[0]) = identity.
       So start balanced = -1 (ub = 0). */
    for (int i = 0; i < width; i++) {
        p = ig_alu_xtor(p, word[i]);
    }
    return p;
}

/**
 * Internal: all-zero detection — TOR fold across word.
 * Result == -1 (ub 0) means all zero.
 */
static trit all_zero_chain(const trit *word, int width)
{
    trit az = TRIT_FALSE;  /* ub(0) = identity for TOR */
    for (int i = 0; i < width; i++) {
        az = ig_alu_tor(az, word[i]);
    }
    return az;
}

void ig_talu_exec(const trit *a, const trit *b, int width,
                  ig_opcode_t opcode, ig_talu_result_t *result)
{
    memset(result, 0, sizeof(*result));
    if (width < 1)  width = 1;
    if (width > 32) width = 32;
    result->width = width;

    trit carry_chain = TRIT_FALSE;  /* ub(0) for addition */

    /* For subtraction: LST carry-in = 1 (ub) = 0 (balanced) = TRIT_UNKNOWN */
    /* Actually: 3's complement subtraction needs carry-in = 1 in unbalanced.
       ub(carry) = 1 → balanced = 0 = TRIT_UNKNOWN */
    trit sub_carry_init = TRIT_UNKNOWN;  /* ub(1) for subtraction carry-in */

    /* Prepare complemented operands for subtraction */
    trit tnot_a[32], tnot_b[32];

    switch (opcode) {
    case IG_OP_NOP: /* D0 */
        for (int i = 0; i < width; i++) {
            result->f01[i] = a[i];
            result->f02[i] = b[i];
        }
        break;

    case IG_OP_AI_TOR_TNOR: /* D1: All Inclusive TOR/TNOR */
    case IG_OP_TOR_TNOR:    /* D2: TOR/TNOR */
        for (int i = 0; i < width; i++) {
            result->f01[i] = ig_alu_tor(a[i], b[i]);
            result->f02[i] = ig_alu_tnor(a[i], b[i]);
        }
        break;

    case IG_OP_AI_TAND_TNAND: /* D3: All Inclusive TAND/TNAND */
    case IG_OP_TAND_TNAND:    /* D4: TAND/TNAND */
        for (int i = 0; i < width; i++) {
            result->f01[i] = ig_alu_tand(a[i], b[i]);
            result->f02[i] = ig_alu_tnand(a[i], b[i]);
        }
        break;

    case IG_OP_XTOR_COMP: /* D5: XTOR / Comparator */
        for (int i = 0; i < width; i++) {
            result->f01[i] = ig_alu_xtor(a[i], b[i]);
            result->f02[i] = ig_alu_comparator(a[i], b[i]);
        }
        break;

    case IG_OP_SUB_BA: /* D6: B - A + carry */
        threes_complement(a, tnot_a, width);
        carry_chain = sub_carry_init;
        for (int i = 0; i < width; i++) {
            trit sum_out, carry_out;
            ig_alu_full_add(tnot_a[i], b[i], carry_chain, &sum_out, &carry_out);
            result->f01[i] = sum_out;
            result->f02[i] = carry_out;
            carry_chain = carry_out;
        }
        result->overflow = carry_chain;
        break;

    case IG_OP_SUB_AB: /* D7: A - B + carry */
        threes_complement(b, tnot_b, width);
        carry_chain = sub_carry_init;
        for (int i = 0; i < width; i++) {
            trit sum_out, carry_out;
            ig_alu_full_add(a[i], tnot_b[i], carry_chain, &sum_out, &carry_out);
            result->f01[i] = sum_out;
            result->f02[i] = carry_out;
            carry_chain = carry_out;
        }
        result->overflow = carry_chain;
        break;

    case IG_OP_ADD: /* D8: A + B + carry */
        carry_chain = TRIT_FALSE;  /* ub(0) = no initial carry */
        for (int i = 0; i < width; i++) {
            trit sum_out, carry_out;
            ig_alu_full_add(a[i], b[i], carry_chain, &sum_out, &carry_out);
            result->f01[i] = sum_out;
            result->f02[i] = carry_out;
            carry_chain = carry_out;
        }
        result->overflow = carry_chain;
        break;
    }

    /* Compute flags */
    result->all_zero  = all_zero_chain(result->f01, width);
    result->parity_a  = parity_chain(a, width);
    result->parity_b  = parity_chain(b, width);
}
