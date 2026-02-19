/**
 * @file trit_cntfet_emu.c
 * @brief seT6 Carbon-Nanotube FET Ternary Gate Emulation — implementation.
 *
 * Multi-diameter CNTFET gate emulation with drift modelling,
 * endurance tracking, and Huawei 3-level threshold mapping.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "trit_cntfet_emu.h"
#include <string.h>

/* ==== Helpers =========================================================== */

static int iabs(int v) { return (v < 0) ? -v : v; }
static int imin(int a, int b) { return (a < b) ? a : b; }
static int imax(int a, int b) { return (a > b) ? a : b; }

/**
 * @brief Simple deterministic PRNG (xorshift32).
 */
static uint32_t xorshift32(uint32_t *state) {
    uint32_t x = *state;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    *state = x;
    return x;
}

/* ==== Public API ======================================================== */

int cntfet_init(trit_cntfet_state_t *st) {
    if (!st) return -1;
    memset(st, 0, sizeof(*st));
    st->initialized = 1;
    return 0;
}

int cntfet_add_device(trit_cntfet_state_t *st, int diam_x1000,
                      int chirality_m, int chirality_n) {
    if (!st || !st->initialized) return -1;
    if (st->device_count >= CNTFET_MAX_DEVICES) return -1;
    if (diam_x1000 <= 0) return -1;

    int idx = st->device_count;
    trit_cntfet_config_t *d = &st->devices[idx];
    memset(d, 0, sizeof(*d));

    d->diameter_nm_x1000 = diam_x1000;
    d->chirality_m = chirality_m;
    d->chirality_n = chirality_n;
    d->vth_mv = cntfet_compute_vth(diam_x1000);
    d->endurance_log10 = CNTFET_ENDURANCE_LOG10;
    d->active = 1;

    st->device_count++;
    return idx;
}

int cntfet_compute_vth(int diam_x1000) {
    /* V_TH(mV) = 200 + (diameter_nm − 1.0) × 500
     * In fixed-point: diam_x1000 is nm×1000, so:
     *   shift = (diam_x1000 - 1000) × 500 / 1000 */
    int shift = ((diam_x1000 - 1000) * 500) / 1000;
    int vth = 200 + shift;
    if (vth < 100) vth = 100;   /* Physical minimum */
    if (vth > 900) vth = 900;   /* Physical cap */
    return vth;
}

trit cntfet_tnand(trit a, trit b) {
    /* Balanced ternary NAND: TNAND(a, b) = −min(a, b) */
    int m = imin(a, b);
    int r = -m;
    if (r < -1) r = -1;
    if (r >  1) r =  1;
    return (trit)r;
}

trit cntfet_tnor(trit a, trit b) {
    /* Balanced ternary TNOR: TNOR(a, b) = −max(a, b) */
    int m = imax(a, b);
    int r = -m;
    if (r < -1) r = -1;
    if (r >  1) r =  1;
    return (trit)r;
}

int cntfet_simulate_drift(trit_cntfet_state_t *st, int device,
                          int cycles, uint32_t seed) {
    if (!st || !st->initialized) return -1;
    if (device < 0 || device >= st->device_count) return -1;
    if (cycles <= 0) return -1;

    trit_cntfet_config_t *d = &st->devices[device];
    if (!d->active) return -1;

    uint32_t rng = seed;

    /*
     * Drift model: sub-linear accumulation (√cycles scaling).
     * drift_increment ≈ sqrt(cycles) / 100, capped at CNTFET_DRIFT_MAX_MV.
     * Add small random walk component for realism.
     */
    /* Integer sqrt of cycles */
    int sqrt_cyc = 1;
    {
        int tmp = cycles;
        int r = tmp / 2;
        if (r == 0) r = 1;
        for (int i = 0; i < 20 && r > 0; i++) {
            int nr = (r + tmp / r) / 2;
            if (nr >= r) break;
            r = nr;
        }
        sqrt_cyc = r;
    }

    /* Base drift increment: sqrt(cycles) / 100, minimum 1 mV per call */
    int base_drift = sqrt_cyc / 100;
    if (base_drift < 1) base_drift = 1;

    /* Random walk: ±1 mV jitter */
    int jitter = (int)(xorshift32(&rng) % 3) - 1;  /* -1, 0, or +1 */
    int drift_inc = base_drift + jitter;
    if (drift_inc < 1) drift_inc = 1;  /* Always accumulate at least 1 mV */

    d->drift_mv += drift_inc;
    d->cycle_count += cycles;
    st->total_cycles += cycles;

    /* Check if drift exceeds max */
    if (iabs(d->drift_mv) > CNTFET_DRIFT_MAX_MV) {
        d->faulted = 1;
        st->total_faulted++;
    }

    if (iabs(d->drift_mv) > CNTFET_DRIFT_MAX_MV / 2)
        st->total_drifted++;

    /* Track worst drift */
    if (iabs(d->drift_mv) > st->max_drift_mv)
        st->max_drift_mv = iabs(d->drift_mv);

    return d->drift_mv;
}

int cntfet_stabilize(trit_cntfet_state_t *st, int device, int threshold_mv) {
    if (!st || !st->initialized) return -1;
    if (device < 0 || device >= st->device_count) return -1;

    trit_cntfet_config_t *d = &st->devices[device];
    if (!d->active) return -1;

    /* Only correct if drift exceeds threshold */
    if (iabs(d->drift_mv) > threshold_mv) {
        /* Feedback correction: halve the drift */
        d->drift_mv = d->drift_mv / 2;
        /* Un-fault if drift is now within spec */
        if (iabs(d->drift_mv) <= CNTFET_DRIFT_MAX_MV)
            d->faulted = 0;
    }

    return iabs(d->drift_mv);
}

int cntfet_check_endurance(trit_cntfet_state_t *st, int device) {
    if (!st || !st->initialized) return -1;
    if (device < 0 || device >= st->device_count) return -1;

    trit_cntfet_config_t *d = &st->devices[device];

    /*
     * Endurance spec: 10^endurance_log10 cycles.
     * Since we can't store 10^12 in int32, we check against
     * a scaled limit: cycles_limit = 10^6 × 10^(log10 - 6).
     * For log10 = 12, limit = 10^6 × 10^6 = 10^12.
     * We compare cycle_count (which is cumulative) against a
     * practical threshold: if cycle_count is a significant
     * fraction of the limit, report concern.
     *
     * Simplified: within spec if cycle_count < 10^6 (since we can't
     * realistically emulate 10^12 operations).
     */
    int limit = 1000000; /* 10^6 practical emulation limit */
    return (d->cycle_count < limit) ? 1 : 0;
}

int cntfet_huawei_class(int vth_mv) {
    if (vth_mv < 150) return -1; /* Below minimum */

    /* Huawei 3-level threshold boundaries:
     *   LVT: 200–300 mV → < 350 mV
     *   MVT: 400 mV     → 350–500 mV
     *   HVT: 600–700 mV → > 500 mV */
    if (vth_mv < 350) return 0;  /* LVT */
    if (vth_mv < 500) return 1;  /* MVT */
    return 2;                    /* HVT */
}

int cntfet_get_avg_vth(const trit_cntfet_state_t *st) {
    if (!st || !st->initialized || st->device_count == 0) return 0;

    int64_t sum = 0;
    int active = 0;
    for (int i = 0; i < st->device_count; i++) {
        if (st->devices[i].active) {
            sum += st->devices[i].vth_mv;
            active++;
        }
    }
    if (active == 0) return 0;
    return (int)(sum / active);
}
