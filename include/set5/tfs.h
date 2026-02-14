/**
 * @file tfs.h
 * @brief seT5 Ternary-Native File System (TFS) — Balanced Ternary Huffman Storage
 *
 * User-space file system module atop STT-MRAM, using Balanced Ternary
 * Huffman Coding for ~40% higher density than binary filesystems.
 *
 * Features:
 *   - Files stored as tryte-chains (variable-length trit blocks)
 *   - Adaptive Balanced Ternary Huffman compression on write
 *   - Trit-tree directory structure (Kleene: -1 left, +1 right, 0 leaf)
 *   - Guardian Trit per block for drift/corruption detection
 *   - Sparse "0" runs consume no physical storage
 *   - POSIX-compatible interface extensions (TFS_OPEN, TFS_READ, etc.)
 *
 * Interfaces through existing POSIX/IPC abstractions — zero kernel changes.
 *
 * @see FRIDAY_JAN13_UPDATES.md — TFS Specification
 * @see stt_mram.h — Underlying ternary MRAM storage
 * @see tipc.h — T-IPC for inter-process file sharing
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET5_TFS_H
#define SET5_TFS_H

#include "set5/trit.h"
#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ========================================================= */

/** Block size in trits (tryte-aligned: 9 trits per tryte) */
#define TFS_BLOCK_TRITS       243      /* 3^5 = 243 trits per block */
#define TFS_MAX_BLOCKS        1024     /* Max blocks in filesystem */
#define TFS_MAX_FILES         128      /* Max files (inodes) */
#define TFS_MAX_DIR_ENTRIES   64       /* Max entries per directory */
#define TFS_MAX_FILENAME      32       /* Max filename length (chars) */
#define TFS_BLOCKS_PER_FILE   16       /* Max blocks per file */
#define TFS_TRYTE_TRITS       9        /* Trits per tryte */

/** Superblock constants */
#define TFS_MAGIC_TRIT_0      TRIT_TRUE     /* Filesystem ID [0] */
#define TFS_MAGIC_TRIT_1      TRIT_FALSE    /* Filesystem ID [1] */
#define TFS_MAGIC_TRIT_2      TRIT_TRUE     /* Filesystem ID [2] */
#define TFS_VERSION           100            /* Version 1.00 */

/** Huffman codes (same as T-IPC — optimized for sparse ternary data):
 *  0 (Unknown) → '0'  (1 bit)   — most frequent in sparse data
 *  +1 (True)   → '10' (2 bits)
 *  -1 (False)  → '11' (2 bits)
 */
#define TFS_HUFF_ZERO_BITS    1
#define TFS_HUFF_POS_BITS     2
#define TFS_HUFF_NEG_BITS     2

/** Compressed block capacity (max bits = TFS_BLOCK_TRITS × 2 worst case) */
#define TFS_COMPRESSED_MAX    64   /* bytes, ceiling(243×2/8) */

/** Performance metrics (×100 scale) */
#define TFS_DENSITY_GAIN_X100   158   /* 1.58 bits/cell vs 1.0 */
#define TFS_AREA_REDUCTION_X100  64   /* 64% of binary area (36% savings) */
#define TFS_WRITE_SPEEDUP_X100   60   /* 0.6× binary write latency */

/* ==== File Modes (trit-valued) ========================================== */

typedef enum {
    TFS_MODE_READ   = -1,   /* Read-only */
    TFS_MODE_WRITE  =  0,   /* Write (create/truncate) */
    TFS_MODE_APPEND =  1    /* Append */
} tfs_mode_t;

/* ==== Commands (POSIX extensions) ======================================= */

typedef enum {
    TFS_CMD_OPEN     = 0x20,
    TFS_CMD_READ     = 0x21,
    TFS_CMD_WRITE    = 0x22,
    TFS_CMD_CLOSE    = 0x23,
    TFS_CMD_SYNC     = 0x24,
    TFS_CMD_COMPRESS = 0x25,
    TFS_CMD_STAT     = 0x26,
    TFS_CMD_UNLINK   = 0x27
} tfs_cmd_t;

/* ==== Data Structures =================================================== */

/** Compressed block */
typedef struct {
    uint8_t data[TFS_COMPRESSED_MAX];
    int     bit_count;          /**< Total compressed bits */
    int     byte_count;         /**< Bytes used */
    int     original_trits;     /**< Pre-compression trit count */
    trit    guardian;            /**< Block checksum (ternary XOR) */
} tfs_compressed_block_t;

/** Data block — raw trit storage */
typedef struct {
    trit    data[TFS_BLOCK_TRITS];
    int     used_trits;         /**< Valid trits in this block */
    trit    guardian;            /**< Checksum */
    int     compressed;         /**< 1 if currently stored compressed */
    tfs_compressed_block_t comp; /**< Compressed form (if compressed==1) */
} tfs_block_t;

/** Inode — file metadata */
typedef struct {
    char    name[TFS_MAX_FILENAME];
    int     valid;              /**< 1=active, 0=deleted */
    int     size_trits;         /**< Total trits stored in file */
    int     block_count;        /**< Number of blocks used */
    int     blocks[TFS_BLOCKS_PER_FILE]; /**< Block indices */
    tfs_mode_t mode;            /**< Current open mode */
    int     open_count;         /**< Open file descriptor count */
    int     write_count;        /**< Total writes to this file */
    int     read_count;         /**< Total reads from this file */
} tfs_inode_t;

/** Directory entry */
typedef struct {
    char    name[TFS_MAX_FILENAME];
    int     inode_idx;          /**< Index into inode table */
    trit    priority;           /**< -1=left, 0=leaf, +1=right (trit-tree) */
} tfs_dirent_t;

/** Filesystem state */
typedef struct {
    /* Superblock */
    trit    magic[3];           /**< Filesystem identifier */
    int     version;
    int     total_blocks;
    int     free_blocks;
    int     total_files;

    /* Storage */
    tfs_block_t  blocks[TFS_MAX_BLOCKS];
    int          block_free[TFS_MAX_BLOCKS]; /**< 1=free, 0=used */
    tfs_inode_t  inodes[TFS_MAX_FILES];

    /* Directory */
    tfs_dirent_t root_dir[TFS_MAX_DIR_ENTRIES];
    int          root_dir_count;

    /* Statistics */
    int     total_reads;
    int     total_writes;
    int     total_compressions;
    int     guardian_checks;
    int     guardian_failures;
    int     initialized;
} tfs_state_t;

/** File descriptor (handle for open files) */
typedef struct {
    int     inode_idx;
    int     cursor_trit;        /**< Read/write cursor position */
    tfs_mode_t mode;
    int     valid;
} tfs_fd_t;

/** Huffman frequency table */
typedef struct {
    int freq_neg;
    int freq_zero;
    int freq_pos;
    int total;
} tfs_freq_t;

/* ==== API ================================================================ */

/**
 * @brief Initialize the TFS filesystem.
 *
 * Sets up superblock, clears all blocks and inodes, initializes root dir.
 */
void tfs_init(tfs_state_t *fs);

/**
 * @brief TFS_OPEN — Open or create a trit-file.
 *
 * @param fs    Filesystem state.
 * @param name  Filename (trit-string, null-terminated).
 * @param mode  -1=read, 0=write (create/truncate), +1=append.
 * @param fd    Output file descriptor.
 * @return 0 on success, -1 on error.
 */
int tfs_open(tfs_state_t *fs, const char *name, tfs_mode_t mode, tfs_fd_t *fd);

/**
 * @brief TFS_WRITE — Write trits to an open file with Huffman compression.
 *
 * @param fs    Filesystem state.
 * @param fd    File descriptor.
 * @param trits Input trit buffer.
 * @param count Number of trits to write.
 * @return Number of trits written, or -1 on error.
 */
int tfs_write(tfs_state_t *fs, tfs_fd_t *fd, const trit *trits, int count);

/**
 * @brief TFS_READ — Read trits from an open file (decompressing if needed).
 *
 * @param fs         Filesystem state.
 * @param fd         File descriptor.
 * @param trits      Output trit buffer.
 * @param max_trits  Maximum trits to read.
 * @return Number of trits read, or -1 on error.
 */
int tfs_read(tfs_state_t *fs, tfs_fd_t *fd, trit *trits, int max_trits);

/**
 * @brief TFS_CLOSE — Close a file descriptor.
 */
int tfs_close(tfs_state_t *fs, tfs_fd_t *fd);

/**
 * @brief TFS_SYNC — Flush and stabilize all blocks of a file.
 *
 * Validates guardian trits for all blocks; recompresses if needed.
 * @return Number of blocks validated, or -1 on error.
 */
int tfs_sync(tfs_state_t *fs, tfs_fd_t *fd);

/**
 * @brief TFS_COMPRESS — In-place recompression of a file's blocks.
 *
 * Rebuilds Huffman for entropy changes (e.g., after many writes).
 * @return Number of blocks recompressed, or -1 on error.
 */
int tfs_compress(tfs_state_t *fs, const char *name);

/**
 * @brief TFS_UNLINK — Delete a file.
 */
int tfs_unlink(tfs_state_t *fs, const char *name);

/**
 * @brief Compute Guardian Trit for a block (ternary XOR checksum).
 */
trit tfs_guardian_compute(const trit *data, int count);

/**
 * @brief Compress a trit buffer using Balanced Ternary Huffman.
 *
 * @param out    Compressed output block.
 * @param trits  Input trit buffer.
 * @param count  Number of trits.
 * @return Compressed bit count, or -1 on error.
 */
int tfs_huffman_encode(tfs_compressed_block_t *out,
                       const trit *trits, int count);

/**
 * @brief Decompress a Huffman-encoded block back to trits.
 *
 * @param trits     Output trit buffer.
 * @param max_trits Maximum trits to decompress.
 * @param comp      Compressed block.
 * @return Number of trits decoded, or -1 on error.
 */
int tfs_huffman_decode(trit *trits, int max_trits,
                       const tfs_compressed_block_t *comp);

/**
 * @brief Count trit frequencies in a buffer.
 */
tfs_freq_t tfs_frequency(const trit *trits, int count);

/**
 * @brief Get filesystem statistics.
 */
void tfs_get_stats(const tfs_state_t *fs, int *files, int *free_blocks,
                   int *reads, int *writes, int *compressions);

/**
 * @brief Get density gain over binary (×100).
 *
 * Returns TFS_DENSITY_GAIN_X100 = 158 (i.e. 1.58× density).
 */
int tfs_density_gain_x100(void);

/**
 * @brief Get area reduction factor (×100).
 *
 * Returns TFS_AREA_REDUCTION_X100 = 64 (i.e. 36% savings).
 */
int tfs_area_reduction_x100(void);

#ifdef __cplusplus
}
#endif

#endif /* SET5_TFS_H */
