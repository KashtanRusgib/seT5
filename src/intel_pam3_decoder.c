/**
 * @file intel_pam3_decoder.c
 * @brief Intel/Prodigy US11405248B2 — FPGA PAM-3 Decoder Pipeline Implementation
 *
 * Implements all 11 stages of the patent's FPGA-based PAM-3 decoding
 * pipeline in software. Each stage is independently testable.
 *
 * The pipeline processes oversampled ADC data (12× symbol rate) through:
 *   DC correction → Level detection → Spike filter → Edge detection →
 *   Midpoint detection → Edge filtering → Sampling → Symbol generation
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/intel_pam3_decoder.h"
#include <string.h>

/* ==================================================================== */
/*  Internal Helpers                                                    */
/* ==================================================================== */

/**
 * @brief Simple xorshift PRNG for noise generation.
 */
static uint32_t pam3d_xorshift(uint32_t *seed)
{
    uint32_t x = *seed;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    *seed = x;
    return x;
}

/**
 * @brief Clamp integer to [0, 255] range (ADC range).
 */
static int clamp_adc(int v)
{
    if (v < 0)   return 0;
    if (v > 255) return 255;
    return v;
}

/**
 * @brief Map trit value to nominal ADC level (8-bit).
 *
 * Mapping: -1 → ~40, 0 → ~128, +1 → ~215
 * These correspond to the three PAM-3 voltage levels centered in
 * the ADC range.
 */
static int trit_to_adc_level(trit t)
{
    switch (t) {
        case TRIT_FALSE:   return 40;    /* Low voltage → low ADC   */
        case TRIT_TRUE:    return 215;   /* High voltage → high ADC */
        default:           return 128;   /* Mid voltage → mid ADC   */
    }
}

/* ==================================================================== */
/*  Initialization                                                      */
/* ==================================================================== */

int pam3d_init(pam3d_decoder_t *dec)
{
    if (!dec) return -1;

    memset(dec, 0, sizeof(*dec));

    /* Default thresholds per patent */
    dec->thresholds.plus_threshold       = 140;
    dec->thresholds.minus_threshold      = 95;
    dec->thresholds.zero_plus_threshold  = 160;
    dec->thresholds.zero_minus_threshold = 80;
    dec->thresholds.dynamic_enabled      = 0;

    /* DC correction defaults */
    dec->dc.enabled             = 1;
    dec->dc.plus_threshold      = 180;  /* MAX must exceed this */
    dec->dc.minus_max_threshold = 70;   /* MIN must be below this */
    dec->dc.block_pos           = 0;
    dec->dc.block_count         = 0;
    dec->dc.block_min           = 255;
    dec->dc.block_max           = 0;

    dec->initialized = 1;
    return 0;
}

int pam3d_set_thresholds(pam3d_decoder_t *dec, const pam3d_thresholds_t *thr)
{
    if (!dec || !thr || !dec->initialized) return -1;
    dec->thresholds = *thr;
    return 0;
}

int pam3d_set_dc_correction(pam3d_decoder_t *dec, int enabled)
{
    if (!dec || !dec->initialized) return -1;
    dec->dc.enabled = enabled ? 1 : 0;
    return 0;
}

/* ==================================================================== */
/*  Stage 1: Load Raw ADC Samples                                      */
/* ==================================================================== */

int pam3d_load_samples(pam3d_decoder_t *dec, const int *samples, int count)
{
    if (!dec || !samples || !dec->initialized) return -1;
    if (count <= 0 || count > PAM3D_MAX_RAW_SAMPLES) return -1;

    /* Copy raw samples into decoder state */
    for (int i = 0; i < count; i++) {
        dec->raw_samples[i] = clamp_adc(samples[i]);
    }
    dec->raw_count = count;

    /* Reset DC correction block tracking */
    dec->dc.block_pos   = 0;
    dec->dc.block_count = 0;
    dec->dc.block_min   = 255;
    dec->dc.block_max   = 0;

    return 0;
}

/* ==================================================================== */
/*  Stage 2: DC Correction                                              */
/* ==================================================================== */

int pam3d_apply_dc_correction(pam3d_decoder_t *dec)
{
    if (!dec || !dec->initialized || dec->raw_count == 0) return -1;

    if (!dec->dc.enabled) {
        /* DC correction disabled — pass through unchanged */
        for (int i = 0; i < dec->raw_count; i++) {
            dec->dc_corrected[i] = dec->raw_samples[i];
        }
        return 0;
    }

    /*
     * Per patent DC correction formula:
     *   Block of 128 samples → compute MAX and MIN.
     *   If MAX > plus_threshold AND MIN < minus_max_threshold
     *     AND (sample - MIN + minus_threshold < 255):
     *       corrected = sample - MIN + minus_threshold
     *   Else:
     *       corrected = sample (no correction)
     *
     * We implement a sliding window approach for efficiency.
     */
    for (int i = 0; i < dec->raw_count; i++) {
        int sample = dec->raw_samples[i];

        /* Update block buffer */
        dec->dc.block[dec->dc.block_pos] = sample;
        dec->dc.block_pos = (dec->dc.block_pos + 1) % PAM3D_DC_BLOCK_LEN;
        if (dec->dc.block_count < PAM3D_DC_BLOCK_LEN)
            dec->dc.block_count++;

        /* Compute MIN and MAX over the current block */
        int bmin = 255, bmax = 0;
        for (int j = 0; j < dec->dc.block_count; j++) {
            int s = dec->dc.block[j];
            if (s < bmin) bmin = s;
            if (s > bmax) bmax = s;
        }

        /* Apply correction if conditions are met */
        if (bmax > dec->dc.plus_threshold &&
            bmin < dec->dc.minus_max_threshold) {
            int corrected = sample - bmin + dec->thresholds.minus_threshold;
            if (corrected < 255) {
                dec->dc_corrected[i] = clamp_adc(corrected);
            } else {
                dec->dc_corrected[i] = sample; /* Would overflow, skip */
            }
        } else {
            dec->dc_corrected[i] = sample; /* Conditions not met, pass-through */
        }
    }

    return 0;
}

/* ==================================================================== */
/*  Stage 3: Slope & Level Detection                                    */
/* ==================================================================== */

int pam3d_detect_levels(pam3d_decoder_t *dec)
{
    if (!dec || !dec->initialized || dec->raw_count == 0) return -1;

    int prev_level = 0; /* Start at 0 (unknown) */

    for (int i = 0; i < dec->raw_count; i++) {
        int current = dec->dc_corrected[i];
        int prev_sample = (i > 0) ? dec->dc_corrected[i - 1] : current;
        int level = prev_level;

        /*
         * First sample or flat region: classify by absolute threshold
         * since there is no slope information yet.
         */
        if (i == 0 || current == prev_sample) {
            /*
             * First sample or flat region: classify by absolute threshold
             * (inclusive) since there is no slope information.
             */
            if (current >= dec->thresholds.plus_threshold)
                level = 1;
            else if (current <= dec->thresholds.minus_threshold)
                level = -1;
            /* else: keep prev_level (mid-range → 0) */
        } else if (current > prev_sample) {
            /*
             * Rising slope: sample going towards +1 or 0.
             * Per patent (thresholds inclusive):
             *   If sample >= plus_threshold → level = +1
             *   Else if sample > zero_minus_threshold → level = 0
             *   Else keep previous level
             */
            if (current >= dec->thresholds.plus_threshold) {
                level = 1;   /* +1 */
            } else if (current > dec->thresholds.zero_minus_threshold) {
                level = 0;   /* 0 */
            }
            /* else: keep prev_level */
        } else if (current < prev_sample) {
            /*
             * Falling slope: sample going towards -1 or 0.
             * Per patent (thresholds inclusive):
             *   If sample <= minus_threshold → level = -1
             *   Else if sample < zero_plus_threshold → level = 0
             *   Else keep previous level
             */
            if (current <= dec->thresholds.minus_threshold) {
                level = -1;  /* -1 */
            } else if (current < dec->thresholds.zero_plus_threshold) {
                level = 0;   /* 0 */
            }
            /* else: keep prev_level */
        }
        /* else: current == prev_sample → keep prev_level */

        dec->pam3_levels[i] = level;
        prev_level = level;
    }

    return 0;
}

/* ==================================================================== */
/*  Stage 4: Spike Filter                                               */
/* ==================================================================== */

int pam3d_spike_filter(pam3d_decoder_t *dec)
{
    if (!dec || !dec->initialized || dec->raw_count == 0) return -1;

    int spikes = 0;

    /*
     * Spike filter per patent FIG. 4F:
     * If a level appears for less than 2 samples and the surrounding
     * levels are the same, it's a spike — replace with surrounding level.
     */
    for (int i = 0; i < dec->raw_count; i++) {
        dec->filtered_levels[i] = dec->pam3_levels[i];
    }

    /* Forward pass: detect and remove single-sample spikes */
    for (int i = 1; i < dec->raw_count - 1; i++) {
        int prev = dec->filtered_levels[i - 1];
        int curr = dec->filtered_levels[i];
        int next = dec->pam3_levels[i + 1];

        /*
         * Spike: current differs from both neighbors, which agree.
         * Example: [+1, -1, +1] → the -1 is a spike.
         */
        if (curr != prev && curr != next && prev == next) {
            dec->filtered_levels[i] = prev;
            spikes++;
        }
    }

    dec->spikes_filtered += spikes;
    return 0;
}

/* ==================================================================== */
/*  Stage 5: Edge Detection                                             */
/* ==================================================================== */

int pam3d_detect_edges(pam3d_decoder_t *dec)
{
    if (!dec || !dec->initialized || dec->raw_count == 0) return -1;

    dec->edge_count = 0;

    for (int i = 1; i < dec->raw_count && dec->edge_count < PAM3D_MAX_EDGES; i++) {
        int prev = dec->filtered_levels[i - 1];
        int curr = dec->filtered_levels[i];

        if (curr != prev) {
            /* Found a transition */
            pam3d_edge_t *edge = &dec->edges[dec->edge_count];
            edge->position = i;
            edge->from_level = prev;
            edge->to_level = curr;
            edge->is_must_transition = 0;
            edge->midpoint = 0;
            edge->retained = 1; /* Initially all edges are retained */

            dec->edge_count++;
            dec->edges_detected++;
        }
    }

    /*
     * Identify "must transitions": +1→-1 or -1→+1 transitions
     * that occur within 12 samples of each other.
     * Per patent: these are critical timing references.
     */
    for (int i = 0; i < dec->edge_count; i++) {
        int from = dec->edges[i].from_level;
        int to   = dec->edges[i].to_level;

        /* Direct +1↔-1 transition is always a must-transition */
        if ((from == 1 && to == -1) || (from == -1 && to == 1)) {
            dec->edges[i].is_must_transition = 1;
            dec->must_transitions_found++;
            continue;
        }

        /* Check if paired transitions within 12 samples form +1↔-1 */
        if (i + 1 < dec->edge_count) {
            int dist = dec->edges[i + 1].position - dec->edges[i].position;
            int final_level = dec->edges[i + 1].to_level;

            if (dist <= PAM3D_MUST_TRANS_WINDOW &&
                ((from == 1 && final_level == -1) ||
                 (from == -1 && final_level == 1))) {
                dec->edges[i].is_must_transition = 1;
                dec->edges[i + 1].is_must_transition = 1;
                dec->must_transitions_found += 2;
            }
        }
    }

    return 0;
}

/* ==================================================================== */
/*  Stage 6: Midpoint Detection                                         */
/* ==================================================================== */

int pam3d_detect_midpoints(pam3d_decoder_t *dec)
{
    if (!dec || !dec->initialized) return -1;

    /*
     * For each must-transition, compute the midpoint sample position.
     * Per patent: midpoint = center of the must-transition region.
     * A zero midpoint indicates invalid (no valid must-transition).
     */
    for (int i = 0; i < dec->edge_count; i++) {
        if (!dec->edges[i].is_must_transition) {
            dec->edges[i].midpoint = 0; /* Invalid */
            continue;
        }

        /* Find the next edge that completes the must-transition pair */
        int start_pos = dec->edges[i].position;
        int end_pos = start_pos;

        for (int j = i + 1; j < dec->edge_count; j++) {
            if (dec->edges[j].is_must_transition &&
                dec->edges[j].position - start_pos <= PAM3D_MUST_TRANS_WINDOW) {
                end_pos = dec->edges[j].position;
                break;
            }
        }

        if (end_pos > start_pos) {
            dec->edges[i].midpoint = (start_pos + end_pos) / 2;
        } else {
            /* Single must-transition: midpoint is the edge position itself */
            dec->edges[i].midpoint = start_pos;
        }
    }

    return 0;
}

/* ==================================================================== */
/*  Stage 7-8: Edge Filtering                                           */
/* ==================================================================== */

int pam3d_filter_edges(pam3d_decoder_t *dec)
{
    if (!dec || !dec->initialized) return -1;

    int removed = 0;

    /*
     * First-level edge filter (per patent):
     *   - Retain all edges corresponding to must-transitions
     *   - Retain edges where distance from previous edge ≥ 9 samples
     *   - Delete all other edges (erroneous transitions)
     */
    int prev_position = -PAM3D_MIN_EDGE_DIST; /* Allow first edge */

    for (int i = 0; i < dec->edge_count; i++) {
        if (dec->edges[i].is_must_transition) {
            dec->edges[i].retained = 1;
            prev_position = dec->edges[i].position;
        } else {
            int dist = dec->edges[i].position - prev_position;
            if (dist >= PAM3D_MIN_EDGE_DIST) {
                dec->edges[i].retained = 1;
                prev_position = dec->edges[i].position;
            } else {
                dec->edges[i].retained = 0;
                removed++;
            }
        }
    }

    /*
     * Second-level edge filter (per patent):
     *   If a non-must edge is followed by a must-transition edge
     *   within the next 4 samples, discard the non-must edge.
     */
    for (int i = 0; i < dec->edge_count; i++) {
        if (!dec->edges[i].retained) continue;
        if (dec->edges[i].is_must_transition) continue;

        /* Check if a must-transition follows within 4 samples */
        for (int j = i + 1; j < dec->edge_count; j++) {
            int dist = dec->edges[j].position - dec->edges[i].position;
            if (dist > PAM3D_EDGE_LOOKAHEAD) break;

            if (dec->edges[j].is_must_transition) {
                dec->edges[i].retained = 0;
                removed++;
                break;
            }
        }
    }

    dec->erroneous_edges_removed += removed;
    return 0;
}

/* ==================================================================== */
/*  Stage 9-10: Sampling Point Calculation                              */
/* ==================================================================== */

int pam3d_calculate_sampling_points(pam3d_decoder_t *dec)
{
    if (!dec || !dec->initialized) return -1;

    dec->sampling_count = 0;
    int prev_sp = 0;

    for (int i = 0; i < dec->edge_count; i++) {
        if (!dec->edges[i].retained) continue;

        int sp;

        /*
         * Per patent sampling point rules:
         *   1. If edge has a non-zero midpoint (must-transition),
         *      use midpoint as sampling point.
         *   2. If no midpoint, use 12th sample from previous SP.
         *   3. If no edges at all, sample every 12th sample.
         */
        if (dec->edges[i].midpoint > 0) {
            sp = dec->edges[i].midpoint;
        } else {
            sp = prev_sp + PAM3D_OVERSAMPLE_RATIO;
        }

        /* Add sampling point if within range */
        if (sp < dec->raw_count && dec->sampling_count < PAM3D_MAX_SYMBOLS) {
            dec->sampling_points[dec->sampling_count] = sp;
            dec->sampling_count++;
            prev_sp = sp;
        }
    }

    /* Fill gaps between edge-derived sampling points with 12-sample intervals */
    if (dec->sampling_count > 0) {
        /*
         * Pre-edge gap: add sampling points for symbol regions that
         * precede the first edge.  Without this, the first symbol
         * would never be sampled when it sits before any transition.
         */
        int first_sp = dec->sampling_points[0];
        if (first_sp > PAM3D_OVERSAMPLE_RATIO / 2) {
            int pre_tmp[PAM3D_MAX_SYMBOLS];
            int pre_count = 0;
            for (int sp = PAM3D_OVERSAMPLE_RATIO / 2;
                 sp < first_sp; sp += PAM3D_OVERSAMPLE_RATIO) {
                pre_tmp[pre_count++] = sp;
            }
            if (pre_count > 0 &&
                pre_count + dec->sampling_count <= PAM3D_MAX_SYMBOLS) {
                /* Shift existing SPs right and prepend */
                for (int k = dec->sampling_count - 1; k >= 0; k--)
                    dec->sampling_points[k + pre_count] =
                        dec->sampling_points[k];
                for (int k = 0; k < pre_count; k++)
                    dec->sampling_points[k] = pre_tmp[k];
                dec->sampling_count += pre_count;
            }
        }

        /* Post-edge gap: fill after last edge-derived SP */
        int last_sp = dec->sampling_points[dec->sampling_count - 1];
        while (last_sp + PAM3D_OVERSAMPLE_RATIO < dec->raw_count &&
               dec->sampling_count < PAM3D_MAX_SYMBOLS) {
            last_sp += PAM3D_OVERSAMPLE_RATIO;
            dec->sampling_points[dec->sampling_count] = last_sp;
            dec->sampling_count++;
        }
    } else {
        /* No edges found — sample every 12th sample */
        for (int sp = PAM3D_OVERSAMPLE_RATIO / 2;
             sp < dec->raw_count && dec->sampling_count < PAM3D_MAX_SYMBOLS;
             sp += PAM3D_OVERSAMPLE_RATIO) {
            dec->sampling_points[dec->sampling_count] = sp;
            dec->sampling_count++;
        }
    }

    /*
     * Sampling point filter (per patent):
     *   - Retain if corresponds to must-transition
     *   - Discard if another SP follows within 4 samples (keep the later one)
     *   - Retain all others
     */
    int removed = 0;
    for (int i = 0; i < dec->sampling_count - 1; i++) {
        int dist = dec->sampling_points[i + 1] - dec->sampling_points[i];
        if (dist > 0 && dist < PAM3D_EDGE_LOOKAHEAD) {
            /* Check if current SP corresponds to a must-transition */
            int is_must = 0;
            for (int j = 0; j < dec->edge_count; j++) {
                if (dec->edges[j].is_must_transition &&
                    dec->edges[j].position == dec->sampling_points[i]) {
                    is_must = 1;
                    break;
                }
            }
            if (!is_must) {
                /* Remove this SP (keep the later one) */
                for (int k = i; k < dec->sampling_count - 1; k++) {
                    dec->sampling_points[k] = dec->sampling_points[k + 1];
                }
                dec->sampling_count--;
                removed++;
                i--; /* Re-check current position */
            }
        }
    }
    dec->erroneous_sp_removed += removed;

    return dec->sampling_count;
}

/* ==================================================================== */
/*  Stage 11: Symbol Generation                                         */
/* ==================================================================== */

int pam3d_generate_symbols(pam3d_decoder_t *dec)
{
    if (!dec || !dec->initialized) return -1;

    dec->symbol_count = 0;

    for (int i = 0; i < dec->sampling_count && i < PAM3D_MAX_SYMBOLS; i++) {
        int sp = dec->sampling_points[i];

        if (sp >= 0 && sp < dec->raw_count) {
            /* Read the filtered PAM-3 level at the sampling point */
            int level = dec->filtered_levels[sp];

            /* Convert to trit */
            switch (level) {
                case  1: dec->decoded_symbols[i] = TRIT_TRUE;    break;
                case -1: dec->decoded_symbols[i] = TRIT_FALSE;   break;
                default: dec->decoded_symbols[i] = TRIT_UNKNOWN; break;
            }
            dec->symbol_count++;
        }
    }

    dec->total_symbols_decoded += dec->symbol_count;
    dec->total_samples_processed += dec->raw_count;

    return dec->symbol_count;
}

/* ==================================================================== */
/*  Full Pipeline Decode                                                */
/* ==================================================================== */

int pam3d_decode_full(pam3d_decoder_t *dec)
{
    if (!dec || !dec->initialized) return -1;
    if (dec->raw_count == 0) return -1;

    /* Run all 11 stages in sequence */
    if (pam3d_apply_dc_correction(dec) < 0) return -1;
    if (pam3d_detect_levels(dec) < 0) return -1;
    if (pam3d_spike_filter(dec) < 0) return -1;
    if (pam3d_detect_edges(dec) < 0) return -1;
    if (pam3d_detect_midpoints(dec) < 0) return -1;
    if (pam3d_filter_edges(dec) < 0) return -1;
    if (pam3d_calculate_sampling_points(dec) < 0) return -1;
    if (pam3d_generate_symbols(dec) < 0) return -1;

    return dec->symbol_count;
}

int pam3d_get_symbols(const pam3d_decoder_t *dec, trit *out, int max)
{
    if (!dec || !out || max <= 0) return -1;

    int count = dec->symbol_count;
    if (count > max) count = max;

    for (int i = 0; i < count; i++) {
        out[i] = dec->decoded_symbols[i];
    }

    return count;
}

/* ==================================================================== */
/*  Test Signal Generator                                               */
/* ==================================================================== */

int pam3d_generate_test_signal(const trit *trits, int trit_count,
                               int *out, int max_out, uint32_t noise_seed)
{
    if (!trits || !out || trit_count <= 0) return -1;

    int total_samples = trit_count * PAM3D_OVERSAMPLE_RATIO;
    if (total_samples > max_out) return -1;

    int idx = 0;
    for (int t = 0; t < trit_count; t++) {
        int level = trit_to_adc_level(trits[t]);

        /*
         * Generate 12 samples per symbol.
         * First and last sample have smooth transitions (ramp).
         */
        for (int s = 0; s < PAM3D_OVERSAMPLE_RATIO; s++) {
            int sample = level;

            /* Add noise if requested */
            if (noise_seed != 0) {
                int noise = (int)(pam3d_xorshift(&noise_seed) % 21) - 10;
                sample = clamp_adc(sample + noise);
            }

            out[idx++] = sample;
        }
    }

    return idx;
}
