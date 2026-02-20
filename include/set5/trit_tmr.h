/**
 * @file trit_tmr.h
 * @brief seT6 Triple Modular Redundancy (TMR) for Ternary Logic
 *
 * Implements portable, verifiable TMR for both scalar K₃ trits and
 * packed64 (32-trit) words.  TMR runs three independent copies of a
 * computation and returns the majority result — a single fault cannot
 * corrupt the output.
 *
 * Key invariants (all proved in proof/TritTMR.thy):
 *   TMR-2:  Single-fault tolerance — if 2 of 3 inputs agree, output = their value.
 *   TMR-5:  No novelty — vote output \<in> inputs ∪ {TRIT_UNKNOWN}.
 *   TMR-6:  Idempotent — trit_tmr_vote3(t, t, t) == t for all valid t.
 *   TMR-7:  Symmetric — result is independent of argument ordering.
 *   no-fault-output: packed64 vote never produces a 0b11 fault slot.
 *
 * Conservation with T-SEC sanitization (proof/PackedFaultSemantics.thy):
 *   Inputs are sanitised before the majority vote so that fault-encoding
 *   0b11 is mapped to 0b00 (UNKNOWN) first; the vote then runs on
 *   {FALSE, UNKNOWN, TRUE} only.  This prevents the lo-bit masquerade
 *   attack documented in Suite 91 / Suite 97.
 *
 * Formal verification reference:
 *   proof/TritTMR.thy — tmr_security_combined, pair_tmr_no_fault_output
 *   proof/PackedFaultSemantics.thy — sanitize_removes_fault
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_TRIT_TMR_H
#define SET6_TRIT_TMR_H

#include "set5/trit.h"   /* trit_sanitize_packed64, has_fault_packed64, trit_pack */
#include <stdint.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C"
{
#endif

    /* ==== Scalar (K₃ trit) TMR ============================================ */

    /**
     * @brief Majority vote over three K₃ trits.
     *
     * Returns the trit agreed upon by at least two of {a, b, c}.
     * If no two agree, returns TRIT_UNKNOWN (conservative default).
     *
     * Proved in TritTMR.thy::tmr_vote.
     *
     * @param a  First trit  (-1, 0, +1)
     * @param b  Second trit
     * @param c  Third trit
     * @return   Majority trit, or TRIT_UNKNOWN if no majority.
     */
    static inline int8_t trit_tmr_vote3(int8_t a, int8_t b, int8_t c)
    {
        if (a == b)
            return a;
        if (b == c)
            return b;
        if (a == c)
            return a;
        return TRIT_UNKNOWN; /* no majority: conservative unknown */
    }

    /**
     * @brief Check if two independent trit readings are consistent.
     *
     * @param a  First reading.
     * @param b  Second reading.
     * @return   true if a == b (agreement), false otherwise.
     */
    static inline bool trit_tmr_agree(int8_t a, int8_t b)
    {
        return a == b;
    }

    /* ==== Packed-64 TMR ================================================== */

    /**
     * @brief Triple modular redundancy vote on three packed-64 trit words.
     *
     * Each word holds 32 ternary values packed as 2-bit slots (see trit.h).
     * Algorithm:
     *   1. Sanitize all three inputs — fault-encoding 0b11 → 0b00 (UNKNOWN).
     *      (prevents lo-bit masquerade, proved in PackedFaultSemantics.thy)
     *   2. Compute per-bit-plane majority: maj(a,b,c) = (a&b)|(b&c)|(a&c).
     *   3. Result is guaranteed in {FALSE, UNKNOWN, TRUE} per slot (0b11 free).
     *
     * Formal invariants:
     *   - No fault slot (0b11) in output:  TRIT_PACKED_VALID(result) is true.
     *   - Single-fault tolerance:  if 2 of 3 inputs agree per slot, output = that.
     *
     * @param a  First  packed-64 word.
     * @param b  Second packed-64 word.
     * @param c  Third  packed-64 word.
     * @return   Per-slot majority, sanitized (no 0b11 slots).
     */
    static inline uint64_t trit_tmr_vote_packed64(uint64_t a, uint64_t b, uint64_t c)
    {
        /* Step 1: sanitize — kills all 0b11 fault slots */
        a = trit_sanitize_packed64(a);
        b = trit_sanitize_packed64(b);
        c = trit_sanitize_packed64(c);

        /* Step 2: separate lo and hi bit planes */
        const uint64_t MASK = 0x5555555555555555ULL;
        uint64_t lo_a = a & MASK;
        uint64_t hi_a = (a >> 1) & MASK;
        uint64_t lo_b = b & MASK;
        uint64_t hi_b = (b >> 1) & MASK;
        uint64_t lo_c = c & MASK;
        uint64_t hi_c = (c >> 1) & MASK;

        /* Step 3: bitwise majority per plane */
        uint64_t lo_r = (lo_a & lo_b) | (lo_b & lo_c) | (lo_a & lo_c);
        uint64_t hi_r = (hi_a & hi_b) | (hi_b & hi_c) | (hi_a & hi_c);

        /* Reconstruct — lo_r | (hi_r << 1) */
        /* Proof that no 0b11 slot can appear:
         *   After sanitize, for every slot i: lo[i]&hi[i] = 0 (no 0b11).
         *   lo_r[i] = 1 requires ≥2 of {lo_a,lo_b,lo_c}[i] = 1 → slot is TRUE in ≥2 inputs.
         *   hi_r[i] = 1 requires ≥2 of {hi_a,hi_b,hi_c}[i] = 1 → slot is FALSE in ≥2 inputs.
         *   lo_r[i]=1 ∧ hi_r[i]=1 would require ≥2 TRUE ∧ ≥2 FALSE simultaneously
         *   among only 3 inputs — impossible (pigeonhole). QED.     */
        return lo_r | (hi_r << 1);
    }

    /**
     * @brief Check whether two packed-64 words agree on all slots.
     *
     * @param a  First  word.
     * @param b  Second word.
     * @return   true if a == b (full agreement), false otherwise.
     */
    static inline bool trit_tmr_agree_packed64(uint64_t a, uint64_t b)
    {
        return a == b;
    }

    /**
     * @brief Check fault-injection divergence between two packed-64 readings.
     *
     * Returns the set of slots where a and b disagree (as a packed-64 word
     * where diverging slots are set to TRUE/0b01 and agreeing to FALSE/0b10).
     * Useful for locating the site of a fault injection.
     *
     * @param a  First  reading.
     * @param b  Second reading.
     * @return   Divergence mask: slot = 0b01 (TRUE) where a[slot] ≠ b[slot],
     *           slot = 0b10 (FALSE) where a[slot] == b[slot].
     */
    static inline uint64_t trit_tmr_divergence_packed64(uint64_t a, uint64_t b)
    {
        uint64_t diff = a ^ b; /* non-zero bits mark differing raw bits   */
        /* For each 2-bit slot: non-zero diff → divergence.
         * Smear: diff_lo = diff | (diff >> 1), keep lo bits.
         * Build TRUE (0b01) for diverging slots, FALSE (0b10) for agreeing slots. */
        const uint64_t MASK = ~0x0ULL; /* all 64 bits */
        (void)MASK;
        /* OR the two bits of each slot together to detect any divergence */
        uint64_t diff_lo = diff & 0x5555555555555555ULL;
        uint64_t diff_hi = (diff >> 1) & 0x5555555555555555ULL;
        uint64_t any_diff = diff_lo | diff_hi; /* 1 in lo-bit position if slot differs */
        /* diverging slot → TRUE (0b01); agreeing slot → FALSE (0b10) */
        return any_diff | ((~any_diff & 0x5555555555555555ULL) << 1);
    }

    /* ==== TMR Ensemble (3-replica compute wrapper) ======================== */

    /**
     * @brief TMR computation result descriptor.
     *
     * Holds the voted result and a fault indicator (whether any replica
     * disagreed, suggesting at least one fault was injected).
     */
    typedef struct
    {
        uint64_t result; /**< Voted packed-64 result (no fault slots). */
        bool fault_seen; /**< true if at least one replica disagreed.  */
    } trit_tmr_result_t;

    /**
     * @brief Run a TMR ensemble: call fn three times and vote.
     *
     * Calls @p fn with @p arg three independent times, votes the results
     * via trit_tmr_vote_packed64, and reports whether any divergence was
     * detected.
     *
     * @param fn   Function to execute redundantly.  Must be deterministic
     *             and side-effect free (pure).
     * @param arg  Single uint64_t argument forwarded to fn.
     * @return     trit_tmr_result_t with voted result and fault indicator.
     */
    static inline trit_tmr_result_t
    trit_tmr_run(uint64_t (*fn)(uint64_t), uint64_t arg)
    {
        uint64_t r0 = fn(arg);
        uint64_t r1 = fn(arg);
        uint64_t r2 = fn(arg);
        trit_tmr_result_t out;
        out.result = trit_tmr_vote_packed64(r0, r1, r2);
        out.fault_seen = !(trit_tmr_agree_packed64(r0, r1) &&
                           trit_tmr_agree_packed64(r1, r2));
        return out;
    }

#ifdef __cplusplus
}
#endif

#endif /* SET6_TRIT_TMR_H */
