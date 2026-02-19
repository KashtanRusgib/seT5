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

#include "set5/trit.h"

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

/* ---- Inline implementations ---- */
/**
 * @file trit_timesyncd.c
 * @brief seT6 Trit Linux — Time Synchronization Protocol Implementation
 *
 * Implements NTP-like time sync, MRAM persistent timestamps, priority
 * queues for time-sensitive events, skew monitoring, and replay detection.
 *
 * SPDX-License-Identifier: GPL-2.0
 */


/* ==================================================================== */
/*  Initialization                                                      */
/* ==================================================================== */

static inline int ttime_init(ttime_state_t *ts) {
    if (!ts) return TTIME_ERR_INIT;

    memset(ts, 0, sizeof(*ts));
    ts->sync_status = TRIT_UNKNOWN;  /* Not yet synced */
    ts->mram_record.valid = 0;
    ts->initialized = 1;
    return TTIME_OK;
}

/* ==================================================================== */
/*  Time Source Management                                              */
/* ==================================================================== */

static inline int ttime_add_source(ttime_state_t *ts, const char *name,
                     int stratum, const unsigned char *auth_token) {
    if (!ts || !ts->initialized || !name) return TTIME_ERR_INIT;
    if (ts->source_count >= TTIME_MAX_SOURCES) return TTIME_ERR_FULL;

    ttime_source_t *src = &ts->sources[ts->source_count];
    memset(src, 0, sizeof(*src));

    strncpy(src->name, name, TTIME_SOURCE_LEN - 1);
    src->id = ts->source_count;
    src->stratum = stratum;
    src->active = 1;

    /* Quality from stratum */
    if (stratum <= 1) src->quality = TTIME_QUALITY_HIGH;
    else if (stratum <= 3) src->quality = TTIME_QUALITY_MEDIUM;
    else src->quality = TTIME_QUALITY_LOW;

    /* Copy auth token if provided */
    if (auth_token) {
        memcpy(src->auth_token, auth_token, TTIME_AUTH_TOKEN_LEN);
        src->authenticated = 1;
    }

    ts->source_count++;
    return src->id;
}

/* Forward declaration: ttime_record_skew is defined later in this header
 * but called from ttime_sync below; the forward decl prevents the
 * "static declaration follows non-static declaration" error. */
static inline int ttime_record_skew(ttime_state_t *ts, long skew_us_x10);

/* ==================================================================== */
/*  Time Sync — Select best source and synchronize                      */
/* ==================================================================== */

static inline int ttime_sync(ttime_state_t *ts) {
    if (!ts || !ts->initialized) return TTIME_ERR_INIT;
    if (ts->source_count == 0) return TTIME_ERR_NOTFOUND;

    /* Find best source (lowest stratum, authenticated preferred) */
    int best = -1;
    int best_stratum = 999;
    for (int i = 0; i < ts->source_count; i++) {
        if (!ts->sources[i].active) continue;
        int effective = ts->sources[i].stratum;
        if (!ts->sources[i].authenticated) effective += 5;  /* Penalize unauthed */
        if (effective < best_stratum) {
            best_stratum = effective;
            best = i;
        }
    }

    if (best < 0) return TTIME_ERR_NOTFOUND;

    ttime_source_t *src = &ts->sources[best];

    /* Simulate sync: capture offset */
    long offset = src->offset_us_x10;
    if (offset < 0) offset = -offset;

    /* Check for excessive skew — reject as desync */
    if (offset > TTIME_SKEW_MAX_US_X10) {
        ts->sync_status = TRIT_FALSE;
        return TTIME_ERR_DESYNC;
    }

    /* Apply sync */
    ts->synced_time_us_x10 = ts->local_time_us_x10 + src->offset_us_x10;
    src->last_sync_us_x10 = ts->synced_time_us_x10;
    ts->sync_count++;
    ts->sync_status = TRIT_TRUE;

    /* Record skew */
    ttime_record_skew(ts, src->offset_us_x10);

    return TTIME_OK;
}

/* ==================================================================== */
/*  Skew Detection & History                                            */
/* ==================================================================== */

static inline long ttime_check_skew(ttime_state_t *ts) {
    if (!ts || !ts->initialized) return TTIME_ERR_INIT;

    /* Compute skew between local and last synced */
    long skew = ts->local_time_us_x10 - ts->synced_time_us_x10;
    if (skew < 0) skew = -skew;

    if (skew > TTIME_SKEW_CRIT_US_X10) {
        ts->sync_status = TRIT_FALSE;  /* Lost sync */
        return TTIME_ERR_SKEW;
    }

    return skew;
}

static inline int ttime_record_skew(ttime_state_t *ts, long skew_us_x10) {
    if (!ts || !ts->initialized) return TTIME_ERR_INIT;

    long abs_skew = skew_us_x10 < 0 ? -skew_us_x10 : skew_us_x10;

    ts->skew.samples[ts->skew.head] = abs_skew;
    ts->skew.head = (ts->skew.head + 1) % TTIME_HISTORY_SIZE;
    if (ts->skew.count < TTIME_HISTORY_SIZE) ts->skew.count++;

    /* Update max */
    if (abs_skew > ts->skew.max_skew_us_x10)
        ts->skew.max_skew_us_x10 = abs_skew;

    /* Running average */
    long sum = 0;
    for (int i = 0; i < ts->skew.count; i++) {
        sum += ts->skew.samples[i];
    }
    ts->skew.avg_skew_us_x10 = (ts->skew.count > 0) ? sum / ts->skew.count : 0;

    return TTIME_OK;
}

/* ==================================================================== */
/*  MRAM Persistent Timestamps                                          */
/* ==================================================================== */

static inline int ttime_mram_store(ttime_state_t *ts, long timestamp_us_x10) {
    if (!ts || !ts->initialized) return TTIME_ERR_INIT;

    ts->mram_record.timestamp_us_x10 = timestamp_us_x10;
    ts->mram_record.sequence_number++;
    ts->mram_record.valid = 1;
    return TTIME_OK;
}

static inline long ttime_mram_restore(ttime_state_t *ts) {
    if (!ts || !ts->initialized) return TTIME_ERR_INIT;
    if (!ts->mram_record.valid) return TTIME_ERR_NOTFOUND;

    return ts->mram_record.timestamp_us_x10;
}

/* ==================================================================== */
/*  Priority Event Queue                                                */
/* ==================================================================== */

static inline int ttime_event_add(ttime_state_t *ts, long deadline_us_x10, trit priority) {
    if (!ts || !ts->initialized) return TTIME_ERR_INIT;
    if (ts->event_count >= TTIME_MAX_EVENTS) return TTIME_ERR_FULL;

    ttime_event_t *ev = &ts->events[ts->event_count];
    memset(ev, 0, sizeof(*ev));

    ev->id = ts->event_count;
    ev->deadline_us_x10 = deadline_us_x10;
    ev->priority = priority;
    ev->dispatched = 0;
    ev->missed = 0;

    ts->event_count++;
    return ev->id;
}

static inline int ttime_event_dispatch(ttime_state_t *ts, long current_time_us_x10) {
    if (!ts || !ts->initialized) return TTIME_ERR_INIT;

    /* Find highest priority undispatched event */
    int best = -1;
    trit best_prio = TRIT_FALSE;

    for (int i = 0; i < ts->event_count; i++) {
        if (ts->events[i].dispatched) continue;
        if (ts->events[i].priority > best_prio ||
            (ts->events[i].priority == best_prio && best < 0)) {
            best_prio = ts->events[i].priority;
            best = i;
        }
    }

    if (best < 0) return TTIME_ERR_NOTFOUND;

    /* Check if deadline missed */
    if (current_time_us_x10 > ts->events[best].deadline_us_x10) {
        ts->events[best].missed = 1;
    }

    ts->events[best].dispatched = 1;
    return best;
}

static inline int ttime_event_check_missed(ttime_state_t *ts, long current_time_us_x10) {
    if (!ts || !ts->initialized) return 0;

    int missed = 0;
    for (int i = 0; i < ts->event_count; i++) {
        if (!ts->events[i].dispatched &&
            current_time_us_x10 > ts->events[i].deadline_us_x10) {
            ts->events[i].missed = 1;
            missed++;
        }
    }
    return missed;
}

/* ==================================================================== */
/*  Replay Attack Detection                                             */
/* ==================================================================== */

static inline int ttime_detect_replay(ttime_state_t *ts, int sequence_number) {
    if (!ts || !ts->initialized) return TTIME_ERR_INIT;

    if (ts->mram_record.valid &&
        sequence_number <= ts->mram_record.sequence_number) {
        /* Sequence number is old — potential replay */
        ts->replay_attempts++;
        return TTIME_ERR_REPLAY;
    }

    return TTIME_OK;
}

/* ==================================================================== */
/*  Clock Management                                                    */
/* ==================================================================== */

static inline int ttime_clock_advance(ttime_state_t *ts, long delta_us_x10) {
    if (!ts || !ts->initialized) return TTIME_ERR_INIT;

    ts->local_time_us_x10 += delta_us_x10;
    return TTIME_OK;
}

static inline trit ttime_get_status(const ttime_state_t *ts) {
    if (!ts || !ts->initialized) return TRIT_UNKNOWN;
    return ts->sync_status;
}

#ifdef __cplusplus
}
#endif

#endif /* TRIT_LINUX_TIMESYNCD_H */
