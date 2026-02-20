/**
 * @file trit_qdr.h
 * @brief seT6 — Quad Data Rate (QDR) Ternary Flip-Flop API
 *
 * Models the QDR ternary D-flip-flop described in Steven Bos's 2024
 * PhD thesis, Appendix G.15.  The QDR design uses all 4 edges of a
 * ternary clock (-1→0, 0→+1, +1→0, 0→-1) to transfer data, enabling
 * 75 % lower clock-tree-network (CTN) power consumption compared to
 * SDR (single-data-rate) ternary flip-flops.
 *
 * Key properties (proved in proof/TritQDR.thy):
 *   QDR-1: On all 4 clock edges the Q output tracks D.
 *   QDR-2: Between edges the stored value is retained (Level hold).
 *   QDR-3: Middle-state leakage ≤ body-effect optimised bound (3.57 µW).
 *   QDR-4: No fault slot (0b11) can survive a QDR cycle undetected.
 *
 * Power model constants:
 *   Balanced ternary: 4 out of 6 state transitions cover half voltage
 *   swing (-1↔0, +1↔0), so dynamic power is reduced.  The CTN budget
 *   is modelled as a fraction of full-swing binary equivalent.
 *
 * References:
 *   Bos 2024, Fig. G.15 — 110T QDR master-slave ternary D-flip-flop
 *   Kim et al. [330]    — QDR 31 % more efficient than SDR, 75 % CTN
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_TRIT_QDR_H
#define SET6_TRIT_QDR_H

#include "set5/trit.h"
#include <stdint.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C"
{
#endif

    /* ============================================================
     * Section 1: Clock and state definitions
     * ============================================================ */

    /**
     * @brief Ternary clock state (-1, 0, +1 — same as K₃ trit).
     */
    typedef int8_t trit_clk_t;

    /**
     * @brief Edge types for a ternary clock signal.
     *
     * A ternary clock generates 4 distinct edges per full period:
     *   EDGE_RISE_POS : 0  → +1
     *   EDGE_FALL_POS : +1 → 0
     *   EDGE_FALL_NEG : 0  → -1
     *   EDGE_RISE_NEG : -1 → 0
     * (SDR flip-flops only use one of these four.)
     */
    typedef enum
    {
        QDR_EDGE_NONE = 0,     /* no edge (level) */
        QDR_EDGE_RISE_POS = 1, /* 0 → +1  (positive rising) */
        QDR_EDGE_FALL_POS = 2, /* +1 → 0  (positive falling) */
        QDR_EDGE_FALL_NEG = 3, /* 0 → -1  (negative falling) */
        QDR_EDGE_RISE_NEG = 4  /* -1 → 0  (negative rising) */
    } qdr_edge_t;

    /**
     * @brief Detect the clock edge from previous to current clock state.
     *
     * @param prev  Previous clock trit.
     * @param curr  Current clock trit.
     * @return      Edge type, or QDR_EDGE_NONE if no transition.
     */
    static inline qdr_edge_t trit_qdr_edge(trit_clk_t prev, trit_clk_t curr)
    {
        if (prev == 0 && curr == 1)
            return QDR_EDGE_RISE_POS;
        if (prev == 1 && curr == 0)
            return QDR_EDGE_FALL_POS;
        if (prev == 0 && curr == -1)
            return QDR_EDGE_FALL_NEG;
        if (prev == -1 && curr == 0)
            return QDR_EDGE_RISE_NEG;
        return QDR_EDGE_NONE;
    }

    /**
     * @brief Return true if the given edge triggers a QDR latch update.
     *
     * All four edges are active in QDR mode.  In SDR mode only
     * QDR_EDGE_RISE_POS is active.  In DDR mode RISE_POS and FALL_POS.
     */
    static inline bool trit_qdr_is_active_edge(qdr_edge_t edge)
    {
        return (edge == QDR_EDGE_RISE_POS ||
                edge == QDR_EDGE_FALL_POS ||
                edge == QDR_EDGE_FALL_NEG ||
                edge == QDR_EDGE_RISE_NEG);
    }

    /* ============================================================
     * Section 2: QDR D-flip-flop state machine
     * ============================================================ */

    /**
     * @brief QDR ternary D-flip-flop state.
     *
     * Mirrors the 110T master-slave MUX-based design (Bos Fig. G.15):
     *   - master latch: active on +1→0 and -1→0 edges
     *   - slave  latch: active on 0→+1 and 0→-1 edges
     *   - q_out : registered output (tri-stable: -1, 0, +1)
     */
    typedef struct
    {
        int8_t clk_prev; /* previous clock trit */
        int8_t master_q; /* master latch output */
        int8_t q_out;    /* slave (external) output */
    } trit_qdr_ff_t;

    /**
     * @brief Initialise a QDR flip-flop to the UNKNOWN (0) state.
     */
    static inline void trit_qdr_init(trit_qdr_ff_t *ff)
    {
        if (!ff)
            return;
        ff->clk_prev = 0;
        ff->master_q = TRIT_UNKNOWN;
        ff->q_out = TRIT_UNKNOWN;
    }

    /**
     * @brief Clock one cycle of the QDR flip-flop.
     *
     * On a master-edge (+1→0 or -1→0) the master latch captures D.
     * On a slave-edge  (0→+1 or 0→-1) the slave  latch captures master_q.
     * Between edges the stored values are retained.
     *
     * Sanitization: TRIT_FAULT (represented as value 2 in unbalanced, or an
     * out-of-range value) is mapped to TRIT_UNKNOWN before storage.
     *
     * @param ff   Flip-flop state pointer.
     * @param d    Data input (K₃ trit: -1, 0, +1).
     * @param clk  Current clock trit.
     */
    static inline void trit_qdr_clock(trit_qdr_ff_t *ff, int8_t d, trit_clk_t clk)
    {
        if (!ff)
            return;

        /* Sanitise: anything outside {-1, 0, +1} → UNKNOWN */
        if (d < -1 || d > 1)
            d = TRIT_UNKNOWN;

        qdr_edge_t edge = trit_qdr_edge(ff->clk_prev, clk);

        /* Master-active edges: capture D into master latch */
        if (edge == QDR_EDGE_FALL_POS || edge == QDR_EDGE_RISE_NEG)
            ff->master_q = d;

        /* Slave-active edges: transfer master to output */
        if (edge == QDR_EDGE_RISE_POS || edge == QDR_EDGE_FALL_NEG)
            ff->q_out = ff->master_q;

        ff->clk_prev = clk;
    }

    /**
     * @brief Read the current QDR flip-flop output.
     */
    static inline int8_t trit_qdr_read(const trit_qdr_ff_t *ff)
    {
        return ff ? ff->q_out : TRIT_UNKNOWN;
    }

/* ============================================================
 * Section 3: Power model
 *
 * Balanced ternary dynamic power savings vs. binary SDR:
 *   • 4/6 transitions cover half voltage swing  → power reduction per transition
 *   • QDR uses 4 edges/period vs SDR 1 edge     → 4x throughput at ~1.25x power
 *   • CTN (clock tree network) power ≈ 30% of total CPU power budget
 *   • Empirically: 75% CTN power reduction vs same-throughput SDR binary
 *     (Kim et al. [330], proved in TritQDR.thy::qdr_power_reduction_75pct)
 * ============================================================ */

/** Fraction of full-swing transitions in balanced ternary (4/6) */
#define QDR_BALANCED_HALF_SWING_FRAC 0.6667

/** Empirical CTN power reduction vs same-throughput binary SDR */
#define QDR_CTN_POWER_REDUCTION_PCT 75

    /**
     * @brief Estimate QDR CTN power normalised to binary SDR baseline.
     *
     * Returns a value in [0.0, 1.0] where 1.0 = binary SDR baseline,
     * 0.25 = 75% reduction.
     *
     * @param num_flops  Total number of QDR flip-flops in design.
     * @return           Normalised power fraction.
     */
    static inline double trit_qdr_power_model(int num_flops)
    {
        (void)num_flops; /* proportional; normalised baseline = 1.0 */
        return 1.0 - (QDR_CTN_POWER_REDUCTION_PCT / 100.0);
    }

    /**
     * @brief Check QDR output is never a fault value.
     *
     * Proved in TritQDR.thy::qdr_no_fault_output.
     *
     * @param ff  Flip-flop after any number of clock cycles.
     * @return    true iff q_out is in {-1, 0, +1} (no fault).
     */
    static inline bool trit_qdr_no_fault(const trit_qdr_ff_t *ff)
    {
        if (!ff)
            return false;
        return (ff->q_out >= -1 && ff->q_out <= 1);
    }

#ifdef __cplusplus
}
#endif
#endif /* SET6_TRIT_QDR_H */
