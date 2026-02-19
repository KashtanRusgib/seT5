/**
 * @file trit_stabilize.c
 * @brief seT6 Trit Stability Engine — implementation.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "trit_stabilize.h"
#include <string.h>
#include <stdlib.h>

/* ==== Internal PRNG (xorshift32, deterministic) ======================== */

static uint32_t tstab_xorshift(uint32_t *seed) {
    uint32_t x = *seed;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    *seed = x;
    return x;
}

/** Return a signed noise sample in [-amplitude, +amplitude] mV. */
static int tstab_noise_sample(tstab_state_t *st) {
    if (st->noise_amplitude_mv == 0) return 0;
    uint32_t r = tstab_xorshift(&st->rng_seed);
    int amp = st->noise_amplitude_mv;
    /* Map [0, UINT32_MAX] to [-amp, +amp] */
    return (int)(r % (2 * (uint32_t)amp + 1)) - amp;
}

/* ==== Trit ↔ Voltage mapping ========================================== */

/** Nominal voltage for each trit value (balanced: -1→0mV, 0→400mV, +1→800mV) */
static int trit_to_voltage(trit t) {
    switch (t) {
        case TRIT_FALSE:   return 0;
        case TRIT_UNKNOWN: return 400;
        case TRIT_TRUE:    return 800;
        default:           return 400; /* safest fallback */
    }
}

/** Voltage to trit with decision boundaries at 200mV and 600mV. */
static trit voltage_to_trit(int mv) {
    if (mv < 200) return TRIT_FALSE;
    if (mv > 600) return TRIT_TRUE;
    return TRIT_UNKNOWN;
}

/* ==== PVT adjustment model ============================================= */

/**
 * Compute voltage shift due to PVT conditions.
 * - Process: slow → +30mV shift, fast → -20mV shift
 * - Voltage: shift proportional to deviation from 800mV
 * - Temperature: +0.5mV per 1°C above 25°C
 */
static int pvt_voltage_shift(const tstab_pvt_config_t *cfg) {
    int shift = 0;

    /* Process corner effect */
    if (cfg->process_corner == TSTAB_CORNER_SLOW)
        shift += 30;
    else if (cfg->process_corner == TSTAB_CORNER_FAST)
        shift -= 20;

    /* Supply voltage effect: ΔV from nominal 800mV */
    shift += (cfg->voltage_mv - 800) / 10;

    /* Temperature effect: 0.5 mV per °C above 25°C
     * Use millidegrees directly to avoid truncation: shift_mV = (T_mC - 25000) / 2000 */
    shift += (cfg->temperature_mc - 25000) / 2000;

    return shift;
}

/* ==== Public API ======================================================= */

int tstab_init(tstab_state_t *st) {
    if (!st) return -1;
    memset(st, 0, sizeof(*st));
    st->initialized = 1;
    st->noise_types = 0;
    st->noise_amplitude_mv = 0;
    st->rng_seed = 0xDEAD1337;
    st->seu_prob_ppm = TSTAB_SEU_PROB_PPM;
    st->worst_snm_mv = 9999; /* Will shrink as we test */
    st->stability_ppm = 1000000; /* Assume perfect until tested */
    return 0;
}

int tstab_configure_noise(tstab_state_t *st, int noise_types,
                          int amplitude_mv, uint32_t seed) {
    if (!st || !st->initialized) return -1;
    if (amplitude_mv < 0) return -1;
    st->noise_types = noise_types;
    st->noise_amplitude_mv = amplitude_mv;
    st->rng_seed = seed;
    return 0;
}

int tstab_configure_seu(tstab_state_t *st, int prob_ppm) {
    if (!st || !st->initialized) return -1;
    if (prob_ppm < 0) return -1;
    st->seu_prob_ppm = prob_ppm;
    return 0;
}

int tstab_generate_pvt_sweep(tstab_state_t *st) {
    if (!st || !st->initialized) return -1;

    static const int corners[] = { -1, 0, 1 };
    static const int voltages[] = { 700, 800, 900 };
    static const int temps[] = { -40000, 25000, 125000 }; /* milli-Celsius */

    int idx = 0;
    for (int c = 0; c < 3; c++) {
        for (int v = 0; v < 3; v++) {
            for (int t = 0; t < 3; t++) {
                if (idx >= TSTAB_MAX_PVT_CONFIGS) break;
                st->pvt_configs[idx].process_corner  = corners[c];
                st->pvt_configs[idx].voltage_mv      = voltages[v];
                st->pvt_configs[idx].temperature_mc   = temps[t];
                idx++;
            }
        }
    }
    st->pvt_config_count = idx;
    return idx;
}

int tstab_test_trit_pvt(tstab_state_t *st, trit input,
                        const tstab_pvt_config_t *config,
                        tstab_pvt_result_t *result) {
    if (!st || !st->initialized || !config || !result) return -1;

    memset(result, 0, sizeof(*result));
    result->input = input;

    /* Convert trit to voltage, apply PVT shift + noise */
    int nominal_mv = trit_to_voltage(input);
    int shift = pvt_voltage_shift(config);
    int noise = tstab_noise_sample(st);
    int final_mv = nominal_mv + shift + noise;

    /* Clamp to [0, 800] */
    if (final_mv < 0) final_mv = 0;
    if (final_mv > 800) final_mv = 800;

    result->noise_mv = noise;
    result->output = voltage_to_trit(final_mv);
    result->flipped = (result->output != input) ? 1 : 0;

    /* Compute signal-to-noise margin (distance to nearest boundary) */
    int d_low  = final_mv - 200;  /* distance to FALSE/UNKNOWN boundary */
    int d_high = 600 - final_mv;  /* distance to UNKNOWN/TRUE boundary */
    if (d_low < 0) d_low = -d_low;
    if (d_high < 0) d_high = -d_high;
    int min_d = (d_low < d_high) ? d_low : d_high;
    result->snm_mv = min_d;

    /* Meta-stability detection */
    if (min_d < TSTAB_METASTABLE_MV) {
        result->metastable = 1;
        /* Simulate recovery attempt */
        int recover_noise = tstab_noise_sample(st);
        int recover_mv = final_mv + recover_noise / 2;
        trit recovered = voltage_to_trit(recover_mv);
        if (recovered == input) {
            result->recovery_cycles = 1 + (TSTAB_METASTABLE_MV - min_d) / 5;
        } else {
            result->recovery_cycles = TSTAB_RECOVERY_CYCLES;
            result->flipped = 1;
            result->output = recovered;
        }
        st->metastable_events++;
        if (result->output == input)
            st->metastable_resolved++;
        else
            st->metastable_failed++;
    }

    /* Update global stats */
    st->total_trits_tested++;
    if (result->flipped)
        st->total_flipped++;
    else
        st->total_stable++;

    if (result->snm_mv < st->worst_snm_mv)
        st->worst_snm_mv = result->snm_mv;

    return 0;
}

int tstab_run_full_sweep(tstab_state_t *st) {
    if (!st || !st->initialized || st->pvt_config_count == 0) return -1;

    int total_flips = 0;
    trit test_values[] = { TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE };

    for (int v = 0; v < 3; v++) {
        for (int c = 0; c < st->pvt_config_count; c++) {
            tstab_pvt_result_t result;
            tstab_test_trit_pvt(st, test_values[v], &st->pvt_configs[c], &result);

            /* Store last result for each config in array (round-robin) */
            if (c < TSTAB_MAX_PVT_CONFIGS) {
                st->pvt_results[c] = result;
            }
            if (result.flipped) total_flips++;
        }
    }

    st->pvt_sweep_done = 1;
    /* Update stability PPM */
    if (st->total_trits_tested > 0) {
        st->stability_ppm = (int)(
            (uint64_t)st->total_stable * 1000000ULL /
            (uint64_t)st->total_trits_tested
        );
    }
    return total_flips;
}

int tstab_inject_seu(tstab_state_t *st, trit *trits, int count, int tick) {
    if (!st || !st->initialized || !trits || count <= 0) return -1;

    int flips = 0;
    for (int i = 0; i < count; i++) {
        uint32_t r = tstab_xorshift(&st->rng_seed);
        if ((int)(r % 1000000) < st->seu_prob_ppm) {
            /* Record event */
            if (st->flip_count < TSTAB_MAX_FLIPS_LOG) {
                tstab_flip_event_t *ev = &st->flips[st->flip_count];
                ev->tick = tick;
                ev->position = i;
                ev->before = trits[i];
                /* Cosmic ray flips to a random other state */
                uint32_t r2 = tstab_xorshift(&st->rng_seed);
                if (trits[i] == TRIT_UNKNOWN) {
                    ev->after = (r2 & 1) ? TRIT_TRUE : TRIT_FALSE;
                } else if (trits[i] == TRIT_TRUE) {
                    ev->after = (r2 & 1) ? TRIT_UNKNOWN : TRIT_FALSE;
                } else {
                    ev->after = (r2 & 1) ? TRIT_UNKNOWN : TRIT_TRUE;
                }
                ev->recovered = 0;
                st->flip_count++;
            }
            /* Apply the flip */
            uint32_t r3 = tstab_xorshift(&st->rng_seed);
            if (trits[i] == TRIT_UNKNOWN)
                trits[i] = (r3 & 1) ? TRIT_TRUE : TRIT_FALSE;
            else if (trits[i] == TRIT_TRUE)
                trits[i] = (r3 & 1) ? TRIT_UNKNOWN : TRIT_FALSE;
            else
                trits[i] = (r3 & 1) ? TRIT_UNKNOWN : TRIT_TRUE;

            flips++;
        }
    }
    return flips;
}

int tstab_recover_seu(tstab_state_t *st, trit *trits,
                      const trit *orig, int count) {
    if (!st || !st->initialized || !trits || !orig || count <= 0) return -1;

    int recovered = 0;
    for (int i = 0; i < count; i++) {
        if (trits[i] != orig[i]) {
            /* SRBC-style recovery: compare against known-good reference */
            trits[i] = orig[i];
            recovered++;
        }
    }

    /* Mark recorded flip events as recovered */
    for (int f = 0; f < st->flip_count; f++) {
        if (!st->flips[f].recovered) {
            int pos = st->flips[f].position;
            if (pos < count && trits[pos] == orig[pos]) {
                st->flips[f].recovered = 1;
                st->flips_recovered++;
            }
        }
    }

    st->flips_permanent = st->flip_count - st->flips_recovered;
    return recovered;
}

int tstab_detect_metastable(tstab_state_t *st, const int *voltages_mv,
                            int count) {
    if (!st || !st->initialized || !voltages_mv || count <= 0) return -1;

    int metastable_count = 0;
    for (int i = 0; i < count; i++) {
        int v = voltages_mv[i];
        /* Check distance to both decision boundaries (200mV and 600mV) */
        int d200 = v - 200;
        int d600 = v - 600;
        if (d200 < 0) d200 = -d200;
        if (d600 < 0) d600 = -d600;
        int min_d = (d200 < d600) ? d200 : d600;
        if (min_d < TSTAB_METASTABLE_MV) {
            metastable_count++;
            st->metastable_events++;
        }
    }
    return metastable_count;
}

int tstab_get_stability_ppm(const tstab_state_t *st) {
    if (!st || !st->initialized) return 0;
    if (st->total_trits_tested == 0) return 1000000;
    return (int)(
        (uint64_t)st->total_stable * 1000000ULL /
        (uint64_t)st->total_trits_tested
    );
}

int tstab_get_worst_snm(const tstab_state_t *st) {
    if (!st || !st->initialized) return 0;
    return st->worst_snm_mv;
}

int tstab_apply_cntfet_drift(tstab_state_t *st, int drift_mv) {
    if (!st || !st->initialized) return -1;
    int abs_drift = (drift_mv < 0) ? -drift_mv : drift_mv;
    /* CNTFET drift adds to noise amplitude */
    st->noise_amplitude_mv += abs_drift;
    return st->noise_amplitude_mv;
}

int tstab_tekum_taper(tstab_state_t *st, int from_trits, int to_trits) {
    if (!st || !st->initialized) return -1;
    if (from_trits < 8 || (from_trits % 2) != 0) return -1;
    if (to_trits < 8 || (to_trits % 2) != 0) return -1;
    if (to_trits >= from_trits) return -1;

    /* Tekum truncation = rounding in balanced ternary.
     * The maximum error from chopping (from - to) trits is < 0.5 ulp.
     * We verify this across all PVT sweep noise margin values.
     *
     * Error model: for each SNM value, encode to tekum at from_trits,
     * truncate to to_trits, and compute the error.               */

    int max_err = 0;
    int k = from_trits - to_trits;  /* trits dropped */

    /* Power of 3 for truncated position weight */
    int pw = 1;
    for (int i = 0; i < k; i++) pw *= 3;

    int count = st->pvt_config_count;
    if (count <= 0) count = 1;

    for (int i = 0; i < count && i < TSTAB_MAX_PVT_CONFIGS; i++) {
        int snm = st->pvt_results[i].snm_mv;
        if (snm <= 0) continue;

        /* Balanced ternary truncation error = value mod 3^k,
         * but in balanced representation this is centered around 0,
         * so max error = (3^k - 1) / 2 */
        int remainder = snm % pw;
        /* Balanced shift: remap to [-half, +half] */
        int half = (pw - 1) / 2;
        if (remainder > half) remainder = pw - remainder;

        /* Error in ulp×1000: remainder / 3^k × 1000 */
        int err_x1000 = (remainder * 1000) / pw;
        if (err_x1000 > max_err) max_err = err_x1000;
    }

    return max_err;  /* Should always be < 500 */
}
