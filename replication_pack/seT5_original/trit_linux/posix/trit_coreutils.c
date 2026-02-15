/**
 * @file trit_coreutils.c
 * @brief Trit Linux — POSIX Userland Coreutils Implementation
 *
 * Implements ternary-native coreutils (trit-ls, trit-grep, trit-cp, etc.)
 * and binary-to-ternary transcoding. All operations run in user-space,
 * interfacing through TFS for storage and posix.h for syscall translation.
 *
 * Enhancement 1: "Full POSIX Userland and Binary Transcoding Tools"
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "trit_coreutils.h"

/* ==================================================================== */
/*  tcore_init — Initialize the POSIX coreutils environment             */
/* ==================================================================== */

int tcore_init(tcore_env_t *env) {
    if (!env) return TCORE_ERR_IO;

    /* Zero out entire environment structure for clean state */
    memset(env, 0, sizeof(*env));

    /* Initialize the TFS filesystem backend */
    tfs_init(&env->fs);

    /* Initialize the POSIX file descriptor table (stdin/stdout/stderr) */
    posix_fd_table_init(&env->fd_table);

    /* Initialize the transcode context (multiradix engine + guard) */
    tcore_transcode_init(&env->transcode);

    env->cmd_count = 0;
    env->errors = 0;
    env->initialized = 1;

    return TCORE_OK;
}

/* ==================================================================== */
/*  tcore_ls — List directory contents from TFS                         */
/* ==================================================================== */

int tcore_ls(tcore_env_t *env, tcore_ls_result_t *result) {
    if (!env || !result || !env->initialized) return TCORE_ERR_IO;

    memset(result, 0, sizeof(*result));
    env->cmd_count++;

    /*
     * Walk TFS inodes to enumerate files. TFS stores up to TFS_MAX_FILES
     * inodes. Each active inode has a non-empty name and a valid block count.
     */
    for (int i = 0; i < TFS_MAX_FILES && result->count < TCORE_MAX_ENTRIES; i++) {
        /* Check if inode is active (valid flag set and name non-empty) */
        if (env->fs.inodes[i].valid && env->fs.inodes[i].name[0] != '\0') {
            tcore_dirent_t *de = &result->entries[result->count];
            strncpy(de->name, env->fs.inodes[i].name, 31);
            de->name[31] = '\0';
            de->size_trits = env->fs.inodes[i].size_trits;
            de->is_directory = 0; /* TFS is flat — no directories yet */

            /*
             * Validity check: if the file has blocks allocated and size > 0,
             * mark as valid. Otherwise mark suspect (U) or corrupted (F).
             */
            if (de->size_trits > 0 && env->fs.inodes[i].block_count > 0) {
                de->validity = TRIT_TRUE;
            } else if (de->size_trits == 0) {
                de->validity = TRIT_UNKNOWN; /* empty but allocated */
            } else {
                de->validity = TRIT_FALSE;   /* corrupted metadata */
            }

            result->total_trits += de->size_trits;
            result->count++;
        }
    }

    return TCORE_OK;
}

/* ==================================================================== */
/*  tcore_cat — Read entire file contents into trit buffer              */
/* ==================================================================== */

int tcore_cat(tcore_env_t *env, const char *path, trit *out, int max_len) {
    if (!env || !path || !out || !env->initialized) return TCORE_ERR_IO;

    env->cmd_count++;

    /* Open file for reading via TFS */
    tfs_fd_t fd;
    int rc = tfs_open(&env->fs, path, TFS_MODE_READ, &fd);
    if (rc != 0) {
        env->errors++;
        return TCORE_ERR_NOTFOUND;
    }

    /* Read up to max_len trits */
    int nread = tfs_read(&env->fs, &fd, out, max_len);
    tfs_close(&env->fs, &fd);

    if (nread < 0) {
        env->errors++;
        return TCORE_ERR_IO;
    }

    return nread;
}

/* ==================================================================== */
/*  tcore_echo — Write trit data to a file                              */
/* ==================================================================== */

int tcore_echo(tcore_env_t *env, const char *path, const trit *data, int len) {
    if (!env || !path || !data || !env->initialized) return TCORE_ERR_IO;
    if (len <= 0) return TCORE_ERR_IO;

    env->cmd_count++;

    /* Open file for writing (creates if not exists) */
    tfs_fd_t fd;
    int rc = tfs_open(&env->fs, path, TFS_MODE_WRITE, &fd);
    if (rc != 0) {
        env->errors++;
        return TCORE_ERR_FULL;
    }

    /* Write trit data to file */
    rc = tfs_write(&env->fs, &fd, data, len);
    tfs_close(&env->fs, &fd);

    if (rc < 0) {
        env->errors++;
        return TCORE_ERR_IO;
    }

    return TCORE_OK;
}

/* ==================================================================== */
/*  tcore_cp — Copy file (read from src, write to dst)                  */
/* ==================================================================== */

int tcore_cp(tcore_env_t *env, const char *src, const char *dst) {
    if (!env || !src || !dst || !env->initialized) return TCORE_ERR_IO;

    env->cmd_count++;

    /* Read entire source file */
    trit buf[TCORE_TRANSCODE_BUF];
    int nread = tcore_cat(env, src, buf, TCORE_TRANSCODE_BUF);
    if (nread < 0) return nread; /* Propagate error */

    /* Decrement cmd_count since cat already incremented it */
    env->cmd_count--;

    /* Write to destination */
    return tcore_echo(env, dst, buf, nread);
}

/* ==================================================================== */
/*  tcore_grep — Search for trit pattern in file data                   */
/* ==================================================================== */

int tcore_grep(tcore_env_t *env, const char *path, const trit *pattern,
               int pat_len, tcore_grep_result_t *result) {
    if (!env || !path || !pattern || !result || !env->initialized)
        return TCORE_ERR_IO;
    if (pat_len <= 0 || pat_len > TCORE_MAX_PATTERN) return TCORE_ERR_IO;

    memset(result, 0, sizeof(*result));
    env->cmd_count++;

    /* Read the entire file into a local buffer */
    trit buf[TCORE_TRANSCODE_BUF];
    int nread = tcore_cat(env, path, buf, TCORE_TRANSCODE_BUF);
    env->cmd_count--; /* cat incremented it */
    if (nread < 0) return nread;

    /*
     * Scan through the buffer looking for pattern matches.
     * A "line" is defined as a segment between runs of TRIT_UNKNOWN.
     * We use a simple sliding window match.
     */
    int line_num = 1;
    int in_unknown_run = 0;

    for (int i = 0; i <= nread - pat_len; i++) {
        /* Track line boundaries (TRIT_UNKNOWN sequences) */
        if (buf[i] == TRIT_UNKNOWN) {
            if (!in_unknown_run) {
                line_num++;
                in_unknown_run = 1;
            }
            continue;
        }
        in_unknown_run = 0;

        /* Try to match pattern at position i */
        int match = 1;
        for (int j = 0; j < pat_len; j++) {
            if (buf[i + j] != pattern[j]) {
                match = 0;
                break;
            }
        }

        if (match && result->match_count < TCORE_MAX_ENTRIES) {
            tcore_grep_match_t *m = &result->matches[result->match_count];
            m->line_number = line_num;
            m->match_length = pat_len;
            /* Copy the matched segment */
            int copy_len = pat_len;
            if (copy_len > TCORE_MAX_LINE) copy_len = TCORE_MAX_LINE;
            memcpy(m->matched_data, &buf[i], sizeof(trit) * copy_len);
            result->match_count++;
        }
    }

    result->lines_scanned = line_num;
    return result->match_count;
}

/* ==================================================================== */
/*  tcore_wc — Count trits, lines, and words                           */
/* ==================================================================== */

int tcore_wc(tcore_env_t *env, const char *path,
             int *trits, int *lines, int *words) {
    if (!env || !path || !env->initialized) return TCORE_ERR_IO;

    env->cmd_count++;

    /* Read file data */
    trit buf[TCORE_TRANSCODE_BUF];
    int nread = tcore_cat(env, path, buf, TCORE_TRANSCODE_BUF);
    env->cmd_count--; /* cat incremented */
    if (nread < 0) return nread;

    /*
     * Count metrics:
     *   trits = total trit count
     *   lines = number of TRIT_UNKNOWN-delimited segments
     *   words = contiguous runs of definite (non-Unknown) trits
     */
    int t = nread;
    int l = 1; /* At least one line if file is non-empty */
    int w = 0;
    int in_word = 0;

    if (nread == 0) {
        l = 0; /* Empty file has 0 lines */
    }

    for (int i = 0; i < nread; i++) {
        if (buf[i] == TRIT_UNKNOWN) {
            if (in_word) {
                w++;
                in_word = 0;
            }
            /* New line on transition to Unknown */
            if (i > 0 && buf[i - 1] != TRIT_UNKNOWN) {
                l++;
            }
        } else {
            in_word = 1;
        }
    }
    /* Close last word if file ends with definite trit */
    if (in_word) w++;

    if (trits) *trits = t;
    if (lines) *lines = l;
    if (words) *words = w;

    return TCORE_OK;
}

/* ==================================================================== */
/*  tcore_rm — Remove (unlink) a file from TFS                         */
/* ==================================================================== */

int tcore_rm(tcore_env_t *env, const char *path) {
    if (!env || !path || !env->initialized) return TCORE_ERR_IO;

    env->cmd_count++;

    int rc = tfs_unlink(&env->fs, path);
    if (rc != 0) {
        env->errors++;
        return TCORE_ERR_NOTFOUND;
    }

    return TCORE_OK;
}

/* ==================================================================== */
/*  tcore_head — Read first N trits from a file                         */
/* ==================================================================== */

int tcore_head(tcore_env_t *env, const char *path, trit *out, int count) {
    if (!env || !path || !out || !env->initialized) return TCORE_ERR_IO;
    if (count <= 0) return 0;

    env->cmd_count++;

    /* Open and read only the first `count` trits */
    tfs_fd_t fd;
    int rc = tfs_open(&env->fs, path, TFS_MODE_READ, &fd);
    if (rc != 0) {
        env->errors++;
        return TCORE_ERR_NOTFOUND;
    }

    int nread = tfs_read(&env->fs, &fd, out, count);
    tfs_close(&env->fs, &fd);

    return (nread >= 0) ? nread : TCORE_ERR_IO;
}

/* ==================================================================== */
/*  tcore_tail — Read last N trits from a file                          */
/* ==================================================================== */

int tcore_tail(tcore_env_t *env, const char *path, trit *out, int count) {
    if (!env || !path || !out || !env->initialized) return TCORE_ERR_IO;
    if (count <= 0) return 0;

    env->cmd_count++;

    /* Read entire file first, then return the tail */
    trit buf[TCORE_TRANSCODE_BUF];
    tfs_fd_t fd;
    int rc = tfs_open(&env->fs, path, TFS_MODE_READ, &fd);
    if (rc != 0) {
        env->errors++;
        return TCORE_ERR_NOTFOUND;
    }

    int total = tfs_read(&env->fs, &fd, buf, TCORE_TRANSCODE_BUF);
    tfs_close(&env->fs, &fd);

    if (total < 0) return TCORE_ERR_IO;

    /* Copy the last `count` trits (or all if file is smaller) */
    int start = (total > count) ? (total - count) : 0;
    int copy_len = total - start;
    memcpy(out, &buf[start], sizeof(trit) * copy_len);

    return copy_len;
}

/* ==================================================================== */
/*  Transcode API — Binary-to-Ternary conversion using RADIX_CONV      */
/* ==================================================================== */

int tcore_transcode_init(tcore_transcode_ctx_t *ctx) {
    if (!ctx) return TCORE_ERR_IO;

    memset(ctx, 0, sizeof(*ctx));

    /* Initialize the multi-radix engine for RADIX_CONV operations */
    multiradix_init(&ctx->mr);

    /* Set up the radix integrity guard with clean state */
    ctx->guard.violations = 0;
    ctx->guard.quarantined = 0;
    ctx->guard.transcoded = 0;
    ctx->guard.guard_status = TRIT_TRUE; /* Clean */

    ctx->cycles_binary = 0;
    ctx->cycles_native = 0;
    ctx->overhead_pct = 0.0;

    return TCORE_OK;
}

int tcore_transcode_bin_to_trit(tcore_transcode_ctx_t *ctx,
                                const int *bin_data, int count,
                                trit *out) {
    if (!ctx || !bin_data || !out || count <= 0) return TCORE_ERR_IO;

    int total_trits = 0;

    for (int i = 0; i < count; i++) {
        /*
         * Use RADIX_CONV to convert each binary integer to balanced ternary.
         * The result is stored in a multi-radix register, then extracted.
         * Each integer produces up to 32 trits (register width).
         */
        int reg_idx = 0; /* Use register 0 as scratch */
        int non_zero = radix_conv_to_ternary(&ctx->mr, reg_idx, bin_data[i]);

        /* Extract trits from the register into output buffer */
        for (int t = 0; t < MR_REG_WIDTH; t++) {
            trit2 packed = trit2_reg32_get(&ctx->mr.regs[reg_idx], t);
            out[i * MR_REG_WIDTH + t] = (trit)trit2_decode(packed);
        }

        total_trits += MR_REG_WIDTH;
        ctx->guard.transcoded++;

        /*
         * Apply 3x penalty: each binary transcode "costs" 3 cycles
         * vs 1 cycle for native ternary operations.
         */
        ctx->cycles_binary += TCORE_PENALTY_FACTOR;
        (void)non_zero; /* Used for telemetry only */
    }

    /* Update overhead metric */
    int total_cycles = ctx->cycles_binary + ctx->cycles_native;
    if (total_cycles > 0) {
        ctx->overhead_pct = ((double)ctx->cycles_binary / total_cycles - 1.0) * 100.0;
        if (ctx->overhead_pct < 0.0) ctx->overhead_pct = 0.0;
    }

    return total_trits;
}

int tcore_radix_validate(tcore_transcode_ctx_t *ctx, const trit *data, int len) {
    if (!ctx || !data) return TCORE_ERR_IO;

    /*
     * Check every trit is in the valid balanced ternary range {-1, 0, +1}.
     * Any value outside this set is a radix integrity violation.
     */
    for (int i = 0; i < len; i++) {
        if (data[i] < TRIT_FALSE || data[i] > TRIT_TRUE) {
            ctx->guard.violations++;
            ctx->guard.quarantined++;
            ctx->guard.guard_status = TRIT_FALSE; /* Compromised */
            return TCORE_ERR_RADIX;
        }
    }

    /* Track native cycles for non-transcoded (pure ternary) operations */
    ctx->cycles_native++;

    return TCORE_OK;
}

double tcore_transcode_overhead(const tcore_transcode_ctx_t *ctx) {
    if (!ctx) return 0.0;
    return ctx->overhead_pct;
}
