/**
 * @file trit_timesyncd.h
 * @brief seT6 — Ternary time synchronization daemon (inline implementation)
 * SPDX-License-Identifier: GPL-2.0
 */
#ifndef TRIT_TIMESYNCD_H
#define TRIT_TIMESYNCD_H

#include <string.h>
#include <stdint.h>
#include "set5/trit.h"

#define TTIME_OK            0
#define TTIME_ERR_INIT     (-1)
#define TTIME_ERR_NOTFOUND (-2)
#define TTIME_ERR_SKEW     (-3)
#define TTIME_ERR_REPLAY   (-4)

#define TTIME_QUALITY_HIGH   2
#define TTIME_QUALITY_MEDIUM 1
#define TTIME_QUALITY_LOW    0

#define TTIME_AUTH_TOKEN_LEN 16

#define TTIME_PRIO_HIGH    1
#define TTIME_PRIO_MEDIUM  0
#define TTIME_PRIO_LOW    (-1)

#define TTIME_MAX_SOURCES 8
#define TTIME_MAX_EVENTS  16
#define TTIME_SKEW_THRESHOLD 100000  /* 10ms in us_x10 */

typedef struct {
    char   name[32];
    int    stratum;
    int    quality;
    int    authenticated;
    long   offset_us_x10;
    unsigned char auth_token[TTIME_AUTH_TOKEN_LEN];
} ttime_source_t;

typedef struct {
    int  valid;
    long timestamp;
    int  sequence_number;
} ttime_mram_record_t;

typedef struct {
    long  samples[64];
    int   count;
    long  avg_skew_us_x10;
} ttime_skew_history_t;

typedef struct {
    int  deadline;
    int  priority;
    int  dispatched;
} ttime_event_t;

typedef struct {
    ttime_source_t      sources[TTIME_MAX_SOURCES];
    int                 source_count;
    long                local_time_us_x10;
    long                synced_time_us_x10;
    trit                sync_status;
    int                 sync_count;
    ttime_mram_record_t mram_record;
    ttime_skew_history_t skew;
    ttime_event_t       events[TTIME_MAX_EVENTS];
    int                 event_count;
    int                 replay_attempts;
    int                 last_valid_seq;
} ttime_state_t;

static inline int ttime_init(ttime_state_t *ts) {
    if (!ts) return TTIME_ERR_INIT;
    memset(ts, 0, sizeof(*ts));
    ts->sync_status = TRIT_UNKNOWN;
    return TTIME_OK;
}

static inline trit ttime_get_status(const ttime_state_t *ts) {
    return ts->sync_status;
}

static inline int ttime_add_source(ttime_state_t *ts, const char *name, int stratum, const unsigned char *auth) {
    if (!ts || ts->source_count >= TTIME_MAX_SOURCES) return -1;
    int id = ts->source_count++;
    memset(&ts->sources[id], 0, sizeof(ttime_source_t));
    strncpy(ts->sources[id].name, name, 31);
    ts->sources[id].stratum = stratum;
    ts->sources[id].quality = (stratum <= 1) ? TTIME_QUALITY_HIGH :
                              (stratum <= 3) ? TTIME_QUALITY_MEDIUM : TTIME_QUALITY_LOW;
    if (auth) {
        ts->sources[id].authenticated = 1;
        memcpy(ts->sources[id].auth_token, auth, TTIME_AUTH_TOKEN_LEN);
    }
    return id;
}

static inline int ttime_sync(ttime_state_t *ts) {
    if (!ts || ts->source_count == 0) return TTIME_ERR_NOTFOUND;
    /* Select best source (lowest stratum, authenticated preferred) */
    int best = 0;
    for (int i = 1; i < ts->source_count; i++) {
        if (ts->sources[i].stratum < ts->sources[best].stratum)
            best = i;
        else if (ts->sources[i].stratum == ts->sources[best].stratum &&
                 ts->sources[i].authenticated > ts->sources[best].authenticated)
            best = i;
    }
    ts->synced_time_us_x10 = ts->local_time_us_x10 + ts->sources[best].offset_us_x10;
    ts->sync_status = TRIT_TRUE;
    ts->sync_count++;
    return TTIME_OK;
}

static inline long ttime_check_skew(ttime_state_t *ts) {
    long diff = ts->local_time_us_x10 - ts->synced_time_us_x10;
    if (diff < 0) diff = -diff;
    if (diff > TTIME_SKEW_THRESHOLD) {
        ts->sync_status = TRIT_FALSE;
        return TTIME_ERR_SKEW;
    }
    return diff;
}

static inline int ttime_record_skew(ttime_state_t *ts, long skew) {
    if (ts->skew.count < 64) ts->skew.samples[ts->skew.count] = skew;
    ts->skew.count++;
    long sum = 0;
    int n = ts->skew.count < 64 ? ts->skew.count : 64;
    for (int i = 0; i < n; i++) sum += ts->skew.samples[i];
    ts->skew.avg_skew_us_x10 = sum / n;
    return TTIME_OK;
}

static inline int ttime_mram_store(ttime_state_t *ts, long timestamp) {
    ts->mram_record.valid = 1;
    ts->mram_record.timestamp = timestamp;
    ts->mram_record.sequence_number++;
    ts->last_valid_seq = ts->mram_record.sequence_number;
    return TTIME_OK;
}

static inline long ttime_mram_restore(ttime_state_t *ts) {
    if (!ts->mram_record.valid) return TTIME_ERR_NOTFOUND;
    return ts->mram_record.timestamp;
}

static inline int ttime_clock_advance(ttime_state_t *ts, long delta) {
    ts->local_time_us_x10 += delta;
    return TTIME_OK;
}

static inline int ttime_event_add(ttime_state_t *ts, int deadline, int priority) {
    if (ts->event_count >= TTIME_MAX_EVENTS) return -1;
    int id = ts->event_count++;
    ts->events[id].deadline = deadline;
    ts->events[id].priority = priority;
    ts->events[id].dispatched = 0;
    return id;
}

static inline int ttime_event_dispatch(ttime_state_t *ts, int current_time) {
    int best = -1;
    for (int i = 0; i < ts->event_count; i++) {
        if (ts->events[i].dispatched) continue;
        if (best < 0 || ts->events[i].priority > ts->events[best].priority)
            best = i;
    }
    if (best >= 0) ts->events[best].dispatched = 1;
    (void)current_time;
    return best;
}

static inline int ttime_event_check_missed(ttime_state_t *ts, int current_time) {
    int missed = 0;
    for (int i = 0; i < ts->event_count; i++)
        if (!ts->events[i].dispatched && ts->events[i].deadline < current_time) missed++;
    return missed;
}

static inline int ttime_detect_replay(ttime_state_t *ts, int seq) {
    if (seq <= ts->last_valid_seq) {
        ts->replay_attempts++;
        return TTIME_ERR_REPLAY;
    }
    ts->last_valid_seq = seq;
    return TTIME_OK;
}

#endif /* TRIT_TIMESYNCD_H */
