/*
 * logger.c - Structured logging per LOGGING.md schema
 *
 * Format: [LEVEL] [TIMESTAMP] [AGENT_ROLE] [TASK_ID] [MESSAGE] [DETAILS]
 * Output: Appends to logfile (if initialized) and stderr.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "../include/logger.h"

/* Internal state */
static FILE *log_fp = NULL;        /* Log file handle */
static LogLevel min_level = LOG_DEBUG;  /* Minimum level to output */
static int initialized = 0;

/* Level name lookup table */
static const char *level_names[] = {
    "DEBUG", "INFO", "WARN", "ERROR"
};

const char *log_level_str(LogLevel level) {
    if (level < LOG_DEBUG || level > LOG_ERROR) {
        return "UNKNOWN";
    }
    return level_names[level];
}

int logger_init(const char *logfile) {
    if (initialized) {
        logger_close();
    }

    if (logfile != NULL) {
        log_fp = fopen(logfile, "a");
        if (log_fp == NULL) {
            fprintf(stderr, "[ERROR] logger_init: Cannot open logfile '%s'\n", logfile);
            return -1;
        }
    }

    initialized = 1;
    return 0;
}

void logger_close(void) {
    if (log_fp != NULL) {
        fflush(log_fp);
        fclose(log_fp);
        log_fp = NULL;
    }
    initialized = 0;
}

void logger_set_level(LogLevel level) {
    min_level = level;
}

void log_entry(LogLevel level, const char *role, const char *task,
               const char *msg, const char *details) {
    if (level < min_level) {
        return;
    }

    /* Generate ISO 8601 timestamp */
    char timestamp[64];
    time_t now = time(NULL);
    struct tm *tm_info = localtime(&now);
    if (tm_info == NULL) {
        snprintf(timestamp, sizeof(timestamp), "0000-00-00T00:00:00");
    } else {
        strftime(timestamp, sizeof(timestamp), "%Y-%m-%dT%H:%M:%S", tm_info);
    }

    /* Default values for NULL params */
    const char *r = role    ? role    : "System";
    const char *t = task    ? task    : "NONE";
    const char *m = msg     ? msg     : "";
    const char *d = details ? details : "{}";

    /* Format: [LEVEL] [TIMESTAMP] [ROLE] [TASK] [MSG] [DETAILS] */
    const char *lvl = log_level_str(level);

    /* Write to logfile if open */
    if (log_fp != NULL) {
        fprintf(log_fp, "[%s] [%s] [%s] [%s] [%s] [%s]\n",
                lvl, timestamp, r, t, m, d);
        fflush(log_fp);
    }

    /* Write to stderr for ERROR and WARN */
    if (level >= LOG_WARN) {
        fprintf(stderr, "[%s] [%s] [%s] [%s] [%s] [%s]\n",
                lvl, timestamp, r, t, m, d);
    }
}
