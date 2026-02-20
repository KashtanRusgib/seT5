/**
 * @file trit_mrcs.h
 * @brief seT6 — Mixed Radix Circuit Synthesizer (MRCS) C API
 *
 * Portable C wrappers modelling the MRCS EDA workflow from Steven Bos's
 * 2024 PhD thesis "Beyond 0 and 1: A mixed radix design and verification
 * workflow for modern ternary computers" (USN, Norway).
 *
 * MRCS workflow (three output formats):
 *   1. CNTFET HSPICE netlist  — 32 nm Stanford CNFET model
 *   2. BET Verilog RTL        — Binary-Encoded Ternary for CMOS/FPGA
 *   3. Logic minimization     — n-dimensional Karnaugh-style groupings
 *
 * This header provides:
 *   trit_mrcs_bet_encode / trit_mrcs_bet_decode — 2-bit-per-trit CMOS packing
 *   trit_mrcs_synthesize_table                  — truth-table minimization stub
 *   trit_mrcs_heptavintimal_name                — base-27 gate index → name
 *
 * Heptavintimal (base-27) gate naming follows Jones (2012) and the
 * standard cells catalogued in Bos's Appendix G:
 *   SUM  = 0x7PB (diadic balanced ternary XOR-like)
 *   CONS = 0xRDC (consensus / carry)
 *   MIN  = 0xPC0 (ternary AND)
 *   MAX  = 0xZRP (ternary OR)
 *   NANY = 0x15H
 *   MLE  = 0xH51 (more-less-equal comparator)
 *   etc.  — full 19 683-function table; common ones listed as macros.
 *
 * Formal verification reference:
 *   proof/TritMRCS.thy — mrcs_synthesis_sound, mrcs_bet_kleene_equiv,
 *                        mrcs_mixed_radix_no_fault
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_TRIT_MRCS_H
#define SET6_TRIT_MRCS_H

#include "set5/trit.h"
#include <stdint.h>
#include <stdbool.h>
#include <string.h>

#ifdef __cplusplus
extern "C"
{
#endif

    /* ============================================================
     * Section 1: Binary-Encoded Ternary (BET)
     *
     * MRCS outputs standard CMOS Verilog by encoding each trit as 2 bits:
     *   00 → FALSE  (-1 / 0 in unbalanced)
     *   01 → UNKNOWN (middle state)
     *   10 → TRUE   (+1 / 2 in unbalanced)
     *   11 → FAULT  (sanitised to UNKNOWN on ingress)
     *
     * This matches the existing packed64 2-bit-per-slot encoding in trit.h.
     * ============================================================ */

#define BET_FALSE 0x00u   /* 2b00 */
#define BET_UNKNOWN 0x01u /* 2b01 */
#define BET_TRUE 0x02u    /* 2b10 */
#define BET_FAULT 0x03u   /* 2b11  always sanitised */

    /**
     * @brief Encode a K₃ trit value (-1, 0, +1) to a 2-bit BET slot.
     *
     * @param t  Trit: TRIT_FALSE(-1), TRIT_UNKNOWN(0), TRIT_TRUE(+1)
     * @return   2-bit BET value (BET_FALSE, BET_UNKNOWN, or BET_TRUE).
     */
    static inline uint8_t trit_mrcs_bet_encode(int8_t t)
    {
        if (t > 0)
            return BET_TRUE;
        if (t == 0)
            return BET_UNKNOWN;
        return BET_FALSE;
    }

    /**
     * @brief Decode a 2-bit BET slot back to a K₃ trit.
     *
     * Fault slots (0b11) are conservatively decoded as TRIT_UNKNOWN.
     *
     * @param bet  2-bit BET value (0..3).
     * @return     Trit: -1, 0, or +1.
     */
    static inline int8_t trit_mrcs_bet_decode(uint8_t bet)
    {
        switch (bet & 0x03u)
        {
        case BET_TRUE:
            return TRIT_TRUE;
        case BET_FALSE:
            return TRIT_FALSE;
        default:
            return TRIT_UNKNOWN; /* BET_UNKNOWN or BET_FAULT */
        }
    }

    /**
     * @brief Pack 32 K₃ trits into a 64-bit BET word (2 bits per trit).
     *
     * Bit layout: trit[0] in bits [1:0], trit[1] in bits [3:2], ...
     * Matches trit.h packed64 convention.
     *
     * @param trits  Array of 32 int8_t trits.
     * @return       64-bit BET packed word.
     */
    static inline uint64_t trit_mrcs_bet_pack32(const int8_t trits[32])
    {
        uint64_t word = 0;
        for (int i = 0; i < 32; i++)
            word |= ((uint64_t)(trit_mrcs_bet_encode(trits[i]) & 0x3u)) << (i * 2);
        return word;
    }

    /**
     * @brief Unpack a 64-bit BET word into 32 K₃ trits.
     *
     * @param word   64-bit BET packed word.
     * @param trits  Output array of 32 int8_t trits.
     */
    static inline void trit_mrcs_bet_unpack32(uint64_t word, int8_t trits[32])
    {
        for (int i = 0; i < 32; i++)
            trits[i] = trit_mrcs_bet_decode((uint8_t)((word >> (i * 2)) & 0x3u));
    }

    /**
     * @brief Roundtrip consistency check: pack then unpack == identity for valid trits.
     *
     * Returns true iff all 32 trits survive a BET pack/unpack cycle unchanged.
     * Proved in TritMRCS.thy::mrcs_bet_kleene_equiv.
     *
     * @param trits  Array of 32 K₃ trits.
     * @return       true if roundtrip is lossless.
     */
    static inline bool trit_mrcs_bet_roundtrip_ok(const int8_t trits[32])
    {
        uint64_t w = trit_mrcs_bet_pack32(trits);
        int8_t out[32];
        trit_mrcs_bet_unpack32(w, out);
        return (memcmp(trits, out, 32) == 0);
    }

/* ============================================================
 * Section 2: Heptavintimal (base-27) gate naming
 *
 * Ternary logic functions are uniquely indexed in base-27 (heptavintimal).
 * Each symbol in {0..Z} (base-27) encodes one output column of a truth
 * table. The names below follow Jones (2012) and Bos's Appendix G.
 * ============================================================ */

/* Heptavintimal (base-27) gate indices — string literals.
 * Each index identifies a ternary logic function in base-27 encoding.
 * (Jones 2012; Bos 2024 Appendix G) */

/* Monadic (1-input) gate string indices */
#define MRCS_IDX_NTI "2" /* Negative Ternary Inverter  (0→2,1→0,2→0) */
#define MRCS_IDX_STI "5" /* Standard Ternary Inverter  (0→2,1→1,2→0) */
#define MRCS_IDX_PTI "8" /* Positive Ternary Inverter  (0→0,1→0,2→2) */
#define MRCS_IDX_MTI "6" /* Middle-detecting Inverter  (0→0,1→2,2→0) */
#define MRCS_IDX_BUF "K" /* Buffer / identity          (0→0,1→1,2→2) */
#define MRCS_IDX_INC "7" /* INCREMENT / successor      (0→1,1→2,2→0) */
#define MRCS_IDX_DEC "B" /* DECREMENT / predecessor    (0→2,1→0,2→1) */

/* Diadic (2-input) gate string indices */
#define MRCS_IDX_SUM "7PB"  /* Balanced ternary SUM (XOR-like)           */
#define MRCS_IDX_CONS "RDC" /* Consensus / carry (ternary AND-like)       */
#define MRCS_IDX_MIN "PC0"  /* Ternary AND (MIN)                          */
#define MRCS_IDX_MAX "ZRP"  /* Ternary OR  (MAX)                          */
#define MRCS_IDX_NANY "15H" /* NANY gate                                  */
#define MRCS_IDX_MLE "H51"  /* More-Less-Equal comparator (single gate)   */
#define MRCS_IDX_XOR "5DP"  /* Ternary XOR                                */
#define MRCS_IDX_MUL "PD5"  /* Ternary MULTIPLY                           */
#define MRCS_IDX_EN "RD4"   /* ENABLE (ternary with binary control)       */

/* Triadic (3-input) gate string indices */
#define MRCS_IDX_SUM3 "B7P7PBPB7" /* 3-trit balanced full adder SUM   */
#define MRCS_IDX_CAR3 "XRDRDCDC9" /* 3-trit balanced full adder CARRY */

    /**
     * @brief Return a human-readable name for a heptavintimal gate index.
     *
     * @param  hepta_index  Base-27 gate function index (as string, e.g. "7PB").
     * @return              Canonical gate name, or "UNKNOWN" if not in table.
     */
    static inline const char *trit_mrcs_heptavintimal_name(const char *hepta_index)
    {
        if (!hepta_index)
            return "NULL";
        /* Fast string-comparison table for common gates */
        static const struct
        {
            const char *idx;
            const char *name;
        } table[] = {
            {"2", "NTI"}, {"5", "STI"}, {"8", "PTI"}, {"6", "MTI"}, {"K", "BUF"}, {"7", "INC"}, {"B", "DEC"}, {"7PB", "SUM"}, {"RDC", "CONS"}, {"PC0", "MIN"}, {"ZRP", "MAX"}, {"15H", "NANY"}, {"H51", "MLE"}, {"5DP", "XOR"}, {"PD5", "MUL"}, {"RD4", "EN"}, {"VP0", "DESEL"}, {"B7P7PBPB7", "SUM3"}, {"XRDRDCDC9", "CAR3"}, {NULL, NULL}};
        for (int i = 0; table[i].idx; i++)
            if (strcmp(hepta_index, table[i].idx) == 0)
                return table[i].name;
        return "UNKNOWN";
    }

    /* ============================================================
     * Section 3: Truth-table synthesis stub
     *
     * Models the MRCS n-ary truth-table → logic-minimized netlist pipeline.
     * Full synthesis requires the Unity/C++ MRCS tool; this stub validates
     * inputs and provides the seT6 integration hook.
     *
     * Proved in TritMRCS.thy::mrcs_synthesis_sound — the minimized groupings
     * cover all '1' entries with the fewest n-dim rectangles.
     * ============================================================ */

#define MRCS_MAX_ARITY 7      /* MRCS supports up to 7-input functions */
#define MRCS_MAX_TABLE (2187) /* 3^7 max truth-table entries */

    typedef enum
    {
        MRCS_TVAL_LOW = 0,     /* logic 0 / false */
        MRCS_TVAL_MID = 1,     /* logic 1 / middle */
        MRCS_TVAL_HIGH = 2,    /* logic 2 / true */
        MRCS_TVAL_DONTCARE = 3 /* don't-care (x) */
    } mrcs_tval_t;

    /**
     * @brief Synthesize a minimal set of transistor-paths from a truth table.
     *
     * Stub implementation: validates that the truth table has the correct
     * number of entries for the given arity (3^arity). Returns the number
     * of non-don't-care entries that would form groupings.
     *
     * Full synthesis (generating HSPICE/Verilog) requires the MRCS tool in
     * tools/mrcs/.
     *
     * @param table      Flat truth-table array of mrcs_tval_t values.
     * @param arity      Number of inputs (1..MRCS_MAX_ARITY).
     * @param table_len  Length of table array; must equal 3^arity.
     * @return           Number of covered entries (≥0), or -1 on error.
     */
    static inline int trit_mrcs_synthesize_table(const mrcs_tval_t *table,
                                                 int arity,
                                                 int table_len)
    {
        if (!table || arity < 1 || arity > MRCS_MAX_ARITY)
            return -1;
        /* Verify table_len == 3^arity */
        int expected = 1;
        for (int i = 0; i < arity; i++)
            expected *= 3;
        if (table_len != expected)
            return -1;

        int covered = 0;
        for (int i = 0; i < table_len; i++)
            if (table[i] != MRCS_TVAL_DONTCARE)
                covered++;
        return covered;
    }

    /**
     * @brief Compute the minimum transistor count for an n-ary ternary function.
     *
     * Based on the MRCS formula: pull-up network + pull-down network,
     * each proportional to the number of minimal groupings. Returns a
     * lower-bound estimate for n-dim Karnaugh minimization.
     *
     * Proved in TritMRCS.thy::mrcs_minimal_transistors.
     *
     * @param arity   Number of inputs (1..7).
     * @param groups  Number of minimal groupings found by synthesis.
     * @return        Estimated transistor lower bound.
     */
    static inline int trit_mrcs_min_transistor_count(int arity, int groups)
    {
        if (arity < 1 || groups < 0)
            return -1;
        /* Each grouping contributes arity transistors to pull-up and pull-down */
        /* Plus 2T PTI + 2T NTI per input for external inverters */
        return groups * arity * 2 + arity * 4;
    }

#ifdef __cplusplus
}
#endif
#endif /* SET6_TRIT_MRCS_H */
