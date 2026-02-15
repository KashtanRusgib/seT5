#ifndef LOGGER_H
#define LOGGER_H

#include <stdio.h>

/* Log levels matching LOGGING.md schema */
typedef enum {
    LOG_DEBUG = 0,
    LOG_INFO  = 1,
    LOG_WARN  = 2,
    LOG_ERROR = 3
} LogLevel;

/*
 * Initialize the logger. Opens logfile for appending.
 * Pass NULL to log to stderr only.
 * Returns 0 on success, -1 on failure.
 */
int logger_init(const char *logfile);

/*
 * Close the logger and flush any buffered output.
 */
void logger_close(void);

/*
 * Set minimum log level. Messages below this level are suppressed.
 */
void logger_set_level(LogLevel level);

/*
 * Log a structured entry per LOGGING.md schema:
 *   [LEVEL] [TIMESTAMP] [AGENT_ROLE] [TASK_ID] [MESSAGE] [DETAILS]
 *
 * Parameters:
 *   level   - ERROR|WARN|INFO|DEBUG
 *   role    - Agent role (e.g., "ParserAgent", "VMAgent")
 *   task    - Task ID from TODOLIST.md (e.g., "TASK-001")
 *   msg     - Concise action message
 *   details - JSON blob or NULL (e.g., {"diff":"...", "test_result":"PASS"})
 */
void log_entry(LogLevel level, const char *role, const char *task,
               const char *msg, const char *details);

/*
 * Convenience macros for common log patterns.
 */
#define LOG_DEBUG_MSG(role, task, msg) \
    log_entry(LOG_DEBUG, (role), (task), (msg), NULL)

#define LOG_INFO_MSG(role, task, msg) \
    log_entry(LOG_INFO, (role), (task), (msg), NULL)

#define LOG_WARN_MSG(role, task, msg) \
    log_entry(LOG_WARN, (role), (task), (msg), NULL)

#define LOG_ERROR_MSG(role, task, msg) \
    log_entry(LOG_ERROR, (role), (task), (msg), NULL)

/*
 * Get the string name for a log level.
 */
const char *log_level_str(LogLevel level);

#endif /* LOGGER_H */
