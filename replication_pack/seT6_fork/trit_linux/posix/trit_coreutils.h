/**
 * @file trit_coreutils.h
 * @brief Trit Linux — POSIX Userland Coreutils Header
 *
 * Defines the interface for ternary-native coreutils (trit-ls, trit-grep,
 * trit-cp, etc.) and binary-to-ternary transcoding via the Radix Integrity
 * Guard. All operations run entirely in user-space, interfacing through
 * the existing posix.h translation layer and TFS for storage.
 *
 * Enhancement 1 from LOGICAL_ENHANCEMENTS_FOR_TRIT_LINUX.md:
 *   "Full POSIX Userland and Binary Transcoding Tools"
 *
 * Key features:
 *   - 10+ trit-coreutils commands (ls, cp, grep, cat, echo, wc, head,
 *     tail, mkdir, rm) backed by TFS
 *   - Binary-to-ternary transcode utility using RADIX_CONV
 *   - Sandboxed execution of transcoded binaries with 3x penalty
 *   - OOB-MM integration for transcoded memory
 *   - Radix Integrity Guard: raises IRQ on radix mismatch
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef TRIT_LINUX_POSIX_COREUTILS_H
#define TRIT_LINUX_POSIX_COREUTILS_H

#include "set6/trit.h"
#include "set6/posix.h"
#include "set6/tfs.h"
#include "set6/multiradix.h"
#include "set6/tipc.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ========================================================= */

#define TCORE_MAX_PATH       128   /* Max path length in trits              */
#define TCORE_MAX_LINE       256   /* Max line length for grep/cat          */
#define TCORE_MAX_ENTRIES    64    /* Max directory listing entries          */
#define TCORE_MAX_PATTERN    64    /* Max grep pattern length               */
#define TCORE_TRANSCODE_BUF  512   /* Transcode buffer size in trits        */
#define TCORE_PENALTY_FACTOR 3     /* Slowdown penalty for non-native code  */

/* ==== Error codes ======================================================= */

#define TCORE_OK             0     /* Success                               */
#define TCORE_ERR_NOTFOUND  (-1)   /* File/directory not found              */
#define TCORE_ERR_PERM      (-2)   /* Permission denied                     */
#define TCORE_ERR_FULL      (-3)   /* Filesystem full                       */
#define TCORE_ERR_BADPATH   (-4)   /* Invalid path                          */
#define TCORE_ERR_RADIX     (-5)   /* Radix integrity violation             */
#define TCORE_ERR_OVERFLOW  (-6)   /* Buffer overflow                       */
#define TCORE_ERR_IO        (-7)   /* I/O error                             */

/* ==== Types ============================================================= */

/**
 * @brief Directory entry for trit-ls listing.
 *
 * Stores name, size (in trits), and file type for each TFS entry.
 */
typedef struct {
    char name[32];        /**< File name (ASCII, max 31 chars + null)     */
    int  size_trits;      /**< File size in trits                         */
    int  is_directory;    /**< 1 = directory, 0 = regular file            */
    trit validity;        /**< T=valid, U=suspect, F=corrupted            */
} tcore_dirent_t;

/**
 * @brief Directory listing result from trit-ls.
 */
typedef struct {
    tcore_dirent_t entries[TCORE_MAX_ENTRIES];
    int            count;       /**< Number of entries returned            */
    int            total_trits; /**< Total trit usage across all entries   */
} tcore_ls_result_t;

/**
 * @brief Grep match result.
 *
 * Stores matched line number and content for trit-grep.
 */
typedef struct {
    int  line_number;     /**< 1-based line number of match               */
    trit matched_data[TCORE_MAX_LINE]; /**< Matched trit data             */
    int  match_length;    /**< Length of matched data in trits             */
} tcore_grep_match_t;

/**
 * @brief Grep result set.
 */
typedef struct {
    tcore_grep_match_t matches[TCORE_MAX_ENTRIES];
    int                match_count; /**< Number of matches found           */
    int                lines_scanned; /**< Total lines scanned             */
} tcore_grep_result_t;

/**
 * @brief Radix Integrity Guard state.
 *
 * Monitors transcoded data for radix purity violations. If non-ternary
 * data is detected, the guard raises an IRQ and quarantines the region.
 */
typedef struct {
    int  violations;      /**< Total radix violations detected             */
    int  quarantined;     /**< Number of quarantined memory regions         */
    int  transcoded;      /**< Total successful transcode operations        */
    trit guard_status;    /**< T=clean, U=degraded, F=compromised          */
} tcore_radix_guard_t;

/**
 * @brief Binary-to-ternary transcode context.
 *
 * Uses RADIX_CONV from multiradix.h for conversion with a 3x slowdown
 * penalty for non-native (binary) code execution.
 */
typedef struct {
    multiradix_state_t mr;       /**< Multi-radix engine for RADIX_CONV   */
    tcore_radix_guard_t guard;   /**< Radix integrity monitor             */
    int    cycles_binary;        /**< Cycles spent in binary transcode    */
    int    cycles_native;        /**< Cycles spent on native ternary ops  */
    double overhead_pct;         /**< Measured overhead percentage         */
} tcore_transcode_ctx_t;

/**
 * @brief POSIX coreutils environment.
 *
 * Master state for all coreutils operations, wrapping TFS for file
 * storage and the POSIX fd table for descriptor management.
 */
typedef struct {
    tfs_state_t       fs;           /**< TFS filesystem instance           */
    posix_fd_table_t  fd_table;     /**< POSIX file descriptor table       */
    tcore_transcode_ctx_t transcode; /**< Transcode context                */
    int               cmd_count;    /**< Total commands executed            */
    int               errors;       /**< Total errors encountered          */
    int               initialized;  /**< 1 = ready to use                  */
} tcore_env_t;

/* ==== Coreutils API ===================================================== */

/**
 * @brief Initialize the POSIX coreutils environment.
 *
 * Sets up TFS, POSIX fd table, and radix integrity guard.
 * Must be called before any other tcore_* function.
 *
 * @param env  Environment to initialize.
 * @return TCORE_OK on success.
 */
int tcore_init(tcore_env_t *env);

/**
 * @brief trit-ls: List directory contents.
 *
 * Scans TFS inodes and returns file entries with names, sizes,
 * and validity states.
 *
 * @param env     Initialized environment.
 * @param result  Output listing result.
 * @return TCORE_OK or error code.
 */
int tcore_ls(tcore_env_t *env, tcore_ls_result_t *result);

/**
 * @brief trit-cat: Concatenate and read file contents.
 *
 * Opens a TFS file and reads all trits into the output buffer.
 *
 * @param env     Initialized environment.
 * @param path    File path (null-terminated ASCII).
 * @param out     Output trit buffer (caller allocates).
 * @param max_len Maximum trits to read.
 * @return Number of trits read, or negative error code.
 */
int tcore_cat(tcore_env_t *env, const char *path, trit *out, int max_len);

/**
 * @brief trit-echo: Write trit data to a file.
 *
 * Creates or overwrites a TFS file with the given trit data.
 *
 * @param env   Initialized environment.
 * @param path  File path.
 * @param data  Trit data to write.
 * @param len   Number of trits.
 * @return TCORE_OK or error code.
 */
int tcore_echo(tcore_env_t *env, const char *path, const trit *data, int len);

/**
 * @brief trit-cp: Copy a file within TFS.
 *
 * Reads all trits from src, writes them to dst.
 *
 * @param env  Initialized environment.
 * @param src  Source file path.
 * @param dst  Destination file path.
 * @return TCORE_OK or error code.
 */
int tcore_cp(tcore_env_t *env, const char *src, const char *dst);

/**
 * @brief trit-grep: Search for a trit pattern in a file.
 *
 * Scans file trits in "lines" (delimited by TRIT_UNKNOWN runs) and
 * matches the given pattern. Returns all matching segments.
 *
 * @param env      Initialized environment.
 * @param path     File path to search.
 * @param pattern  Trit pattern to search for.
 * @param pat_len  Length of pattern.
 * @param result   Output match results.
 * @return Number of matches, or negative error code.
 */
int tcore_grep(tcore_env_t *env, const char *path, const trit *pattern,
               int pat_len, tcore_grep_result_t *result);

/**
 * @brief trit-wc: Count trits, "lines", and "words" in a file.
 *
 * A "line" is delimited by sequences of TRIT_UNKNOWN.
 * A "word" is a contiguous run of definite trits (non-Unknown).
 *
 * @param env         Initialized environment.
 * @param path        File path.
 * @param[out] trits  Total trit count.
 * @param[out] lines  Line count.
 * @param[out] words  Word count.
 * @return TCORE_OK or error code.
 */
int tcore_wc(tcore_env_t *env, const char *path, int *trits, int *lines, int *words);

/**
 * @brief trit-rm: Remove (unlink) a file from TFS.
 *
 * @param env   Initialized environment.
 * @param path  File path to remove.
 * @return TCORE_OK or error code.
 */
int tcore_rm(tcore_env_t *env, const char *path);

/**
 * @brief trit-head: Read the first N trits from a file.
 *
 * @param env    Initialized environment.
 * @param path   File path.
 * @param out    Output trit buffer.
 * @param count  Number of trits to read.
 * @return Number of trits actually read, or negative error code.
 */
int tcore_head(tcore_env_t *env, const char *path, trit *out, int count);

/**
 * @brief trit-tail: Read the last N trits from a file.
 *
 * @param env    Initialized environment.
 * @param path   File path.
 * @param out    Output trit buffer.
 * @param count  Number of trits to read from end.
 * @return Number of trits actually read, or negative error code.
 */
int tcore_tail(tcore_env_t *env, const char *path, trit *out, int count);

/* ==== Transcode API ===================================================== */

/**
 * @brief Initialize the binary-to-ternary transcoder.
 *
 * Sets up RADIX_CONV engine and radix integrity guard.
 *
 * @param ctx  Transcode context to initialize.
 * @return TCORE_OK on success.
 */
int tcore_transcode_init(tcore_transcode_ctx_t *ctx);

/**
 * @brief Transcode a binary integer array to balanced ternary.
 *
 * Converts each binary integer using RADIX_CONV and stores the
 * balanced ternary representation in the output trit buffer.
 *
 * @param ctx       Transcode context.
 * @param bin_data  Array of binary integers to convert.
 * @param count     Number of integers.
 * @param out       Output trit buffer (must hold count * 32 trits).
 * @return Total trits written, or negative error code.
 */
int tcore_transcode_bin_to_trit(tcore_transcode_ctx_t *ctx,
                                const int *bin_data, int count,
                                trit *out);

/**
 * @brief Validate trit data for radix purity.
 *
 * Checks that all trit values are in {-1, 0, +1}. Values outside
 * this range trigger the radix integrity guard.
 *
 * @param ctx   Transcode context (guard updated).
 * @param data  Trit data to validate.
 * @param len   Length of data.
 * @return TCORE_OK if pure, TCORE_ERR_RADIX if violations found.
 */
int tcore_radix_validate(tcore_transcode_ctx_t *ctx, const trit *data, int len);

/**
 * @brief Get the current overhead percentage for transcoded operations.
 *
 * @param ctx  Transcode context.
 * @return Overhead as percentage (0.0 = no overhead, 200.0 = 3x slower).
 */
double tcore_transcode_overhead(const tcore_transcode_ctx_t *ctx);

#ifdef __cplusplus
}
#endif

#endif /* TRIT_LINUX_POSIX_COREUTILS_H */
