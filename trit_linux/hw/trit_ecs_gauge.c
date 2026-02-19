/**
 * @file trit_ecs_gauge.c
 * @brief seT6 ECS Gauge-Block Module — implementation.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "trit_ecs_gauge.h"
#include <string.h>

/* ==== Internal helpers ================================================= */

/** Convert voltage to balanced trit with standard decision boundaries. */
static trit ecs_voltage_to_trit(int mv) {
    if (mv < 200) return TRIT_FALSE;
    if (mv > 600) return TRIT_TRUE;
    return TRIT_UNKNOWN;
}

/** Nominal voltage for a trit value. */
static int ecs_trit_to_voltage(trit t) {
    switch (t) {
        case TRIT_FALSE:   return 0;
        case TRIT_UNKNOWN: return 400;
        case TRIT_TRUE:    return 800;
        default:           return 400;
    }
}

/** Absolute value helper. */
static int ecs_abs(int v) { return (v < 0) ? -v : v; }

/** Log an audit entry. */
static void ecs_log_audit(ecs_gauge_state_t *st, int channel,
                          ecs_severity_t sev, trit expected, trit observed,
                          int drift_mv, int corrected) {
    if (st->audit_count >= ECS_MAX_AUDIT_LOG) return;
    ecs_audit_entry_t *e = &st->audit_log[st->audit_count++];
    e->tick      = st->tick;
    e->channel   = channel;
    e->severity  = sev;
    e->expected  = expected;
    e->observed  = observed;
    e->drift_mv  = drift_mv;
    e->corrected = corrected;
}

/* ==== Public API ======================================================= */

int ecs_init(ecs_gauge_state_t *st) {
    if (!st) return -1;
    memset(st, 0, sizeof(*st));
    st->initialized = 1;
    st->health = TRIT_TRUE; /* Start healthy */
    return 0;
}

int ecs_register_channel(ecs_gauge_state_t *st, trit reference, int voltage_mv) {
    if (!st || !st->initialized) return -1;
    if (st->monitor_count >= ECS_MAX_MONITORS) return -1;
    if (reference < -1 || reference > 1) return -1;

    int idx = st->monitor_count;
    ecs_monitor_t *mon = &st->monitors[idx];
    memset(mon, 0, sizeof(*mon));
    mon->active = 1;
    mon->reference = reference;
    mon->current = ecs_voltage_to_trit(voltage_mv);
    mon->voltage_mv = voltage_mv;
    mon->drift_mv = ecs_abs(voltage_mv - ecs_trit_to_voltage(reference));
    mon->status = ECS_MON_TRACKING;
    mon->hesitation = 0;

    st->monitor_count++;
    return idx;
}

int ecs_update_reading(ecs_gauge_state_t *st, int channel, int voltage_mv) {
    if (!st || !st->initialized) return -1;
    if (channel < 0 || channel >= st->monitor_count) return -1;

    ecs_monitor_t *mon = &st->monitors[channel];
    if (!mon->active) return -1;

    mon->voltage_mv = voltage_mv;
    mon->current = ecs_voltage_to_trit(voltage_mv);
    mon->drift_mv = ecs_abs(voltage_mv - ecs_trit_to_voltage(mon->reference));

    return 0;
}

int ecs_tick(ecs_gauge_state_t *st) {
    if (!st || !st->initialized) return -1;

    st->tick++;
    int needs_attention = 0;
    int any_flip = 0;
    int any_drift = 0;

    for (int i = 0; i < st->monitor_count; i++) {
        ecs_monitor_t *mon = &st->monitors[i];
        if (!mon->active) continue;

        trit observed = mon->current;

        /* Check for trit flip */
        if (observed != mon->reference) {
            if (observed == TRIT_UNKNOWN && mon->reference != TRIT_UNKNOWN) {
                /* Hesitation: drifted into Unknown zone */
                mon->hesitation++;
                if (mon->hesitation >= ECS_HESITATION_MAX) {
                    mon->status = ECS_MON_HESITATING;
                    st->hesitation_pauses++;
                    ecs_log_audit(st, i, ECS_SEV_WARNING, mon->reference,
                                  observed, mon->drift_mv, 0);
                    needs_attention++;
                    any_drift = 1;
                }
            } else {
                /* Actual flip */
                mon->flip_count++;
                st->total_flips++;
                mon->status = ECS_MON_FAULTED;
                ecs_log_audit(st, i, ECS_SEV_CRITICAL, mon->reference,
                              observed, mon->drift_mv, 0);
                needs_attention++;
                any_flip = 1;
            }
        } else {
            mon->hesitation = 0; /* Reset on healthy reading */
        }

        /* Check drift threshold */
        if (mon->drift_mv > ECS_DRIFT_THRESH_MV && mon->status == ECS_MON_TRACKING) {
            ecs_log_audit(st, i, ECS_SEV_INFO, mon->reference,
                          observed, mon->drift_mv, 0);
            any_drift = 1;
        }

        /* Scheduled recalibration — guard tick > 0 to avoid spurious recal at init */
        if (st->tick > 0 && st->tick % ECS_RECAL_INTERVAL == 0 && mon->status != ECS_MON_FAULTED) {
            mon->status = ECS_MON_RECALIBRATING;
            /* Reset voltage to nominal (self-healing) */
            int nominal = ecs_trit_to_voltage(mon->reference);
            mon->voltage_mv = nominal;
            mon->current = mon->reference;
            mon->drift_mv = 0;
            mon->hesitation = 0;
            mon->recal_count++;
            st->total_recals++;
            mon->status = ECS_MON_TRACKING;
        }
    }

    /* Update health trit */
    if (any_flip)
        st->health = TRIT_FALSE;
    else if (any_drift)
        st->health = TRIT_UNKNOWN;
    else
        st->health = TRIT_TRUE;

    return needs_attention;
}

int ecs_irq_recalibrate(ecs_gauge_state_t *st) {
    if (!st || !st->initialized) return -1;

    int corrected = 0;
    st->irq_pending = 0;

    for (int i = 0; i < st->monitor_count; i++) {
        ecs_monitor_t *mon = &st->monitors[i];
        if (!mon->active) continue;

        if (mon->status == ECS_MON_FAULTED || mon->status == ECS_MON_HESITATING) {
            /* Force recalibration to nominal */
            int nominal = ecs_trit_to_voltage(mon->reference);
            mon->voltage_mv = nominal;
            mon->current = mon->reference;
            mon->drift_mv = 0;
            mon->hesitation = 0;
            mon->recal_count++;
            mon->status = ECS_MON_TRACKING;
            st->total_recals++;
            st->total_recovered++;
            corrected++;

            /* Log recovery */
            ecs_log_audit(st, i, ECS_SEV_INFO, mon->reference,
                          mon->current, 0, 1);
        }
    }

    /* If all recovered, restore health */
    if (corrected > 0) {
        st->health = TRIT_TRUE;
    }

    return corrected;
}

int ecs_audit_count(const ecs_gauge_state_t *st) {
    if (!st || !st->initialized) return 0;
    return st->audit_count;
}

int ecs_audit_get(const ecs_gauge_state_t *st, int index,
                  ecs_audit_entry_t *out) {
    if (!st || !st->initialized || !out) return -1;
    if (index < 0 || index >= st->audit_count) return -1;
    *out = st->audit_log[index];
    return 0;
}

trit ecs_get_health(const ecs_gauge_state_t *st) {
    if (!st || !st->initialized) return TRIT_FALSE;
    return st->health;
}

int ecs_get_hesitation_count(const ecs_gauge_state_t *st) {
    if (!st || !st->initialized) return 0;
    return st->hesitation_pauses;
}

int ecs_cntfet_endurance(const ecs_gauge_state_t *st,
                         int *endurance_ok, int *endurance_warn) {
    if (!st || !st->initialized || !endurance_ok || !endurance_warn) return -1;

    *endurance_ok = 0;
    *endurance_warn = 0;

    /* CNTFET endurance practical limit for emulation: 10^6 cycles.
     * "warn" threshold: 80% of limit = 800000 cycles. */
    int limit = 1000000;
    int warn_thresh = 800000;

    for (int i = 0; i < st->monitor_count; i++) {
        const ecs_monitor_t *mon = &st->monitors[i];
        if (!mon->active) continue;

        /* Use recal_count as proxy for cycle count */
        int cycles = mon->recal_count * 100;  /* Each recal ≈ 100 cycles */

        if (cycles < warn_thresh)
            (*endurance_ok)++;
        else if (cycles < limit)
            (*endurance_warn)++;
        /* else: exceeded — not counted as ok */
    }

    return 0;
}
