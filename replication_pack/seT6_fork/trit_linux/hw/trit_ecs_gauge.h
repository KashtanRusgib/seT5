/**
 * @file trit_ecs_gauge.h
 * @brief seT6 ECS (Equilibrium Calibration System) Gauge-Block Module
 *
 * Self-calibrating runtime module implementing the "digital gauge block"
 * architecture. Ties SRBC feedback loops to runtime IRQ handling and
 * T-Audit fault logging. Prevents trit-flips from cosmic rays, EM
 * interference, and thermal drift via continuous monitoring.
 *
 * Key features:
 *   - Continuous background calibration loop (tick-driven)
 *   - IRQ-triggered emergency recalibration
 *   - T-Audit fault log (persistent event history)
 *   - Meta-stable state monitoring with "hesitation" counter
 *   - Self-referencing circuit emulation (bias feedback)
 *   - Process corner health reporting
 *   - Integration with SRBC for reference-cell comparison
 *
 * @see srbc.h for gauge-block calibration primitives
 * @see trit_stabilize.h for PVT corner testing
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_TRIT_ECS_GAUGE_H
#define SET6_TRIT_ECS_GAUGE_H

#include "set6/trit.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ======================================================== */

#define ECS_MAX_AUDIT_LOG    128   /**< Max T-Audit fault events */
#define ECS_MAX_MONITORS     16    /**< Max monitored trit channels */
#define ECS_RECAL_INTERVAL   100   /**< Ticks between scheduled recals */
#define ECS_DRIFT_THRESH_MV  20    /**< Drift threshold for alarm */
#define ECS_HESITATION_MAX   10    /**< Consecutive unknowns before pause */

/** Fault severity levels */
typedef enum {
    ECS_SEV_INFO,              /**< Informational drift event */
    ECS_SEV_WARNING,           /**< Approaching margin boundary */
    ECS_SEV_CRITICAL,          /**< Trit flip detected */
    ECS_SEV_EMERGENCY          /**< Multiple flips / cascade */
} ecs_severity_t;

/** Monitor status */
typedef enum {
    ECS_MON_IDLE,
    ECS_MON_TRACKING,
    ECS_MON_RECALIBRATING,
    ECS_MON_HESITATING,        /**< Unknown-state pause */
    ECS_MON_FAULTED
} ecs_mon_status_t;

/* ==== Structures ======================================================= */

/**
 * @brief T-Audit fault log entry.
 */
typedef struct {
    int             tick;          /**< When the event occurred */
    int             channel;       /**< Which monitor channel */
    ecs_severity_t  severity;      /**< Fault severity */
    trit            expected;      /**< Expected trit value */
    trit            observed;      /**< Actual observed value */
    int             drift_mv;      /**< Voltage drift at time of event */
    int             corrected;     /**< 1 if self-corrected */
} ecs_audit_entry_t;

/**
 * @brief Monitored trit channel state (self-referencing circuit).
 */
typedef struct {
    int             active;        /**< Channel is being monitored */
    trit            reference;     /**< Known-good reference value */
    trit            current;       /**< Current observed value */
    int             voltage_mv;    /**< Current analog voltage */
    int             drift_mv;      /**< Accumulated drift */
    int             hesitation;    /**< Consecutive unknown readings */
    ecs_mon_status_t status;
    int             recal_count;   /**< Number of recalibrations */
    int             flip_count;    /**< Number of detected flips */
} ecs_monitor_t;

/**
 * @brief ECS Gauge-Block engine state.
 */
typedef struct {
    int             initialized;

    /* Monitor array */
    ecs_monitor_t   monitors[ECS_MAX_MONITORS];
    int             monitor_count;

    /* Audit log */
    ecs_audit_entry_t audit_log[ECS_MAX_AUDIT_LOG];
    int             audit_count;

    /* Global state */
    int             tick;          /**< Current tick counter */
    int             total_recals;  /**< Total recalibration events */
    int             total_flips;   /**< Total trit flips detected */
    int             total_recovered; /**< Flips successfully self-healed */
    int             irq_pending;   /**< Emergency recal IRQ pending */
    int             hesitation_pauses; /**< Times system paused on Unknown */
    trit            health;        /**< Overall health: TRUE/UNKNOWN/FALSE */
} ecs_gauge_state_t;

/* ==== API ============================================================== */

/**
 * @brief Initialize ECS gauge-block engine.
 * @param st  State to initialize.
 * @return 0 on success, -1 on NULL.
 */
int ecs_init(ecs_gauge_state_t *st);

/**
 * @brief Register a trit channel for continuous monitoring.
 * @param st         State.
 * @param reference  Known-good reference value.
 * @param voltage_mv Initial voltage reading.
 * @return Channel index (0-based), or -1 on error.
 */
int ecs_register_channel(ecs_gauge_state_t *st, trit reference, int voltage_mv);

/**
 * @brief Update a channel's voltage reading (e.g., from ADC).
 * @param st       State.
 * @param channel  Channel index.
 * @param voltage_mv  New voltage reading.
 * @return 0 on success, -1 on error.
 */
int ecs_update_reading(ecs_gauge_state_t *st, int channel, int voltage_mv);

/**
 * @brief Execute one calibration tick.
 *
 * Checks all monitors for drift, triggers recalibration if
 * threshold exceeded, logs T-Audit events for flips/warnings.
 * Increments hesitation counter for Unknown-state channels.
 *
 * @param st  State.
 * @return Number of channels needing attention (0 = all healthy).
 */
int ecs_tick(ecs_gauge_state_t *st);

/**
 * @brief Trigger emergency recalibration (IRQ handler).
 *
 * Forces immediate recalibration of all channels.
 *
 * @param st  State.
 * @return Number of channels corrected.
 */
int ecs_irq_recalibrate(ecs_gauge_state_t *st);

/**
 * @brief Query number of T-Audit log entries.
 * @param st  State.
 * @return Audit entry count.
 */
int ecs_audit_count(const ecs_gauge_state_t *st);

/**
 * @brief Get a T-Audit log entry.
 * @param st     State.
 * @param index  Entry index.
 * @param out    Output entry.
 * @return 0 on success, -1 on error.
 */
int ecs_audit_get(const ecs_gauge_state_t *st, int index,
                  ecs_audit_entry_t *out);

/**
 * @brief Get overall system health trit.
 *
 * TRUE = all channels stable, UNKNOWN = some drifting,
 * FALSE = flips detected.
 *
 * @param st  State.
 * @return Health trit.
 */
trit ecs_get_health(const ecs_gauge_state_t *st);

/**
 * @brief Get count of hesitation pauses (Unknown-state events).
 * @param st  State.
 * @return Number of hesitation pauses.
 */
int ecs_get_hesitation_count(const ecs_gauge_state_t *st);

/**
 * @brief CNTFET endurance check for all monitors.
 *
 * Compares accumulated cycle counts against the CNTFET 10^12
 * endurance spec.  Returns number of monitors within spec.
 *
 * @param st              ECS gauge state.
 * @param endurance_ok    Output: number of monitors within endurance spec.
 * @param endurance_warn  Output: number of monitors at >80% endurance.
 * @return 0 on success, -1 on error.
 */
int ecs_cntfet_endurance(const ecs_gauge_state_t *st,
                         int *endurance_ok, int *endurance_warn);

#ifdef __cplusplus
}
#endif

#endif /* SET6_TRIT_ECS_GAUGE_H */
