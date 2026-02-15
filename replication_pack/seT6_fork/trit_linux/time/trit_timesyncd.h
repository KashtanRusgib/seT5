/**
 * @file trit_timesyncd.h
 * @brief seT6 Trit Linux — Time Synchronization Protocol Header
 *
 * Implements Arch Linux–inspired time synchronization for seT6:
 *   - NTP-like ternary time daemon (chrony-equivalent)
 *   - STT-MRAM non-volatile timestamps for crash recovery
 *   - Trit priority queues for time-sensitive events
 *   - Time skew detection and drift monitoring
 *   - Authenticated time sync (replay attack mitigation)
 *   - Deterministic timing enforcement for multi-radix ops
 *
 * Uses the existing STT-MRAM and scheduler infrastructure — zero kernel mods.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef TRIT_LINUX_TIMESYNCD_H
#define TRIT_LINUX_TIMESYNCD_H

#include "set6/trit.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ========================================================= */

#define TTIME_MAX_SOURCES      8      /* Max NTP-like time sources          */
#define TTIME_MAX_EVENTS       32     /* Max time-sensitive event queue     */
#define TTIME_SOURCE_LEN       32     /* Max source name length             */
#define TTIME_HISTORY_SIZE     16     /* Skew history samples               */

/* Sync quality levels */
#define TTIME_QUALITY_HIGH     2      /* Stratum 1 equivalent              */
#define TTIME_QUALITY_MEDIUM   1      /* Stratum 2-3 equivalent            */
#define TTIME_QUALITY_LOW      0      /* Unsynchronized                    */

/* Trit priority for event queue (maps to scheduler priority) */
#define TTIME_PRIO_HIGH        TRIT_TRUE     /* +1: immediate dispatch     */
#define TTIME_PRIO_MEDIUM      TRIT_UNKNOWN  /*  0: normal scheduling      */
#define TTIME_PRIO_LOW         TRIT_FALSE    /* -1: deferred processing    */

/* Skew thresholds (microseconds, x10 for int math) */
#define TTIME_SKEW_WARN_US_X10     10000    /* 1ms warning threshold       */
#define TTIME_SKEW_CRIT_US_X10    100000    /* 10ms critical threshold     */
#define TTIME_SKEW_MAX_US_X10    1000000    /* 100ms — reject as invalid   */

/* Auth token size */
#define TTIME_AUTH_TOKEN_LEN   16

/* Error codes */
#define TTIME_OK                0
#define TTIME_ERR_INIT         (-1)
#define TTIME_ERR_FULL         (-2)
#define TTIME_ERR_NOTFOUND     (-3)
#define TTIME_ERR_SKEW         (-4)
#define TTIME_ERR_AUTH         (-5)
#define TTIME_ERR_REPLAY       (-6)
#define TTIME_ERR_DESYNC       (-7)

/* ==== Types ============================================================= */

/**
 * @brief Time source descriptor (NTP peer equivalent).
 */
typedef struct {
    char  name[TTIME_SOURCE_LEN];      /**< Source name / address           */
    int   id;                          /**< Source ID                       */
    int   quality;                     /**< TTIME_QUALITY_*                 */
    int   stratum;                     /**< NTP stratum level (1-15)        */
    int   active;                      /**< 1 = source is reachable         */

    /* Timestamps (microseconds since epoch, x10 for precision) */
    long  last_sync_us_x10;           /**< Last sync timestamp             */
    long  offset_us_x10;              /**< Offset from local clock         */
    long  delay_us_x10;               /**< Round-trip delay                */
    long  jitter_us_x10;              /**< Jitter measurement              */

    /* Auth */
    unsigned char auth_token[TTIME_AUTH_TOKEN_LEN]; /**< Auth key          */
    int   authenticated;               /**< 1 = auth verified              */
} ttime_source_t;

/**
 * @brief Time-sensitive event in the priority queue.
 */
typedef struct {
    int   id;                          /**< Event ID                       */
    long  deadline_us_x10;            /**< Deadline (absolute, x10 us)    */
    trit  priority;                    /**< TTIME_PRIO_*                   */
    int   dispatched;                  /**< 1 = already dispatched         */
    int   missed;                      /**< 1 = deadline missed            */
} ttime_event_t;

/**
 * @brief Skew history for drift monitoring.
 */
typedef struct {
    long  samples[TTIME_HISTORY_SIZE]; /**< Skew samples (x10 us)          */
    int   head;                        /**< Circular buffer head           */
    int   count;                       /**< Number of valid samples        */
    long  avg_skew_us_x10;            /**< Running average skew           */
    long  max_skew_us_x10;            /**< Maximum observed skew          */
} ttime_skew_history_t;

/**
 * @brief MRAM timestamp record (non-volatile, survives power loss).
 */
typedef struct {
    long  timestamp_us_x10;           /**< Stored timestamp               */
    int   valid;                       /**< 1 = record is valid            */
    int   sequence_number;             /**< For replay detection           */
} ttime_mram_record_t;

/**
 * @brief Time synchronization daemon state.
 */
typedef struct {
    /* Sources */
    ttime_source_t     sources[TTIME_MAX_SOURCES];
    int                source_count;

    /* Event queue */
    ttime_event_t      events[TTIME_MAX_EVENTS];
    int                event_count;

    /* Skew tracking */
    ttime_skew_history_t skew;

    /* MRAM persistent timestamps */
    ttime_mram_record_t mram_record;

    /* Clock state */
    long  local_time_us_x10;          /**< Local clock (x10 us)           */
    long  synced_time_us_x10;         /**< Last synced time               */
    int   sync_count;                  /**< Total syncs performed          */
    int   replay_attempts;             /**< Detected replay attacks        */
    trit  sync_status;                 /**< +1=synced, 0=syncing, -1=lost  */

    int   initialized;
} ttime_state_t;

/* ==== API =============================================================== */

/** Initialize the time sync daemon. */
int ttime_init(ttime_state_t *ts);

/** Add a time source (NTP peer). */
int ttime_add_source(ttime_state_t *ts, const char *name,
                     int stratum, const unsigned char *auth_token);

/** Perform time sync with best source. */
int ttime_sync(ttime_state_t *ts);

/** Check for time skew (returns skew in x10 us, or error). */
long ttime_check_skew(ttime_state_t *ts);

/** Record skew sample to history. */
int ttime_record_skew(ttime_state_t *ts, long skew_us_x10);

/** Store timestamp to MRAM (non-volatile). */
int ttime_mram_store(ttime_state_t *ts, long timestamp_us_x10);

/** Restore timestamp from MRAM. */
long ttime_mram_restore(ttime_state_t *ts);

/** Add a time-sensitive event to the priority queue. */
int ttime_event_add(ttime_state_t *ts, long deadline_us_x10, trit priority);

/** Dispatch next highest-priority event. */
int ttime_event_dispatch(ttime_state_t *ts, long current_time_us_x10);

/** Check for missed deadlines. */
int ttime_event_check_missed(ttime_state_t *ts, long current_time_us_x10);

/** Detect replay attack (checks sequence number). */
int ttime_detect_replay(ttime_state_t *ts, int sequence_number);

/** Advance local clock by delta_us_x10. */
int ttime_clock_advance(ttime_state_t *ts, long delta_us_x10);

/** Get sync status. */
trit ttime_get_status(const ttime_state_t *ts);

#ifdef __cplusplus
}
#endif

#endif /* TRIT_LINUX_TIMESYNCD_H */
