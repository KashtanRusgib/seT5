/**
 * @file tfs.c
 * @brief seT6 Ternary-Native File System (TFS) — Implementation
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set6/tfs.h"
#include <string.h>
#include <stdio.h>

/* ---- Internal helpers ------------------------------------------------- */

/** Balanced ternary addition mod 3 (for guardian computation) */
static trit trit_xor3(trit a, trit b) {
    int sum = (int)a + (int)b;
    if (sum >  1) sum -= 3;
    if (sum < -1) sum += 3;
    return (trit)sum;
}

/** Find a free block */
static int find_free_block(tfs_state_t *fs) {
    for (int i = 0; i < fs->total_blocks; i++) {
        if (fs->block_free[i]) return i;
    }
    return -1;
}

/** Find inode by name */
static int find_inode(tfs_state_t *fs, const char *name) {
    for (int i = 0; i < TFS_MAX_FILES; i++) {
        if (fs->inodes[i].valid &&
            strncmp(fs->inodes[i].name, name, TFS_MAX_FILENAME) == 0)
            return i;
    }
    return -1;
}

/** Allocate a new inode */
static int alloc_inode(tfs_state_t *fs) {
    for (int i = 0; i < TFS_MAX_FILES; i++) {
        if (!fs->inodes[i].valid) return i;
    }
    return -1;
}

/* ---- Huffman encode/decode (shared with T-IPC scheme) ----------------- */

/** Set bit in compressed buffer */
static void set_bit(tfs_compressed_block_t *c, int pos, int val) {
    int byte_idx = pos / 8;
    int bit_idx  = 7 - (pos % 8);
    if (byte_idx < TFS_COMPRESSED_MAX) {
        if (val)
            c->data[byte_idx] |= (uint8_t)(1 << bit_idx);
        else
            c->data[byte_idx] &= (uint8_t)~(1 << bit_idx);
    }
}

/** Get bit from compressed buffer */
static int get_bit(const tfs_compressed_block_t *c, int pos) {
    int byte_idx = pos / 8;
    int bit_idx  = 7 - (pos % 8);
    if (byte_idx >= TFS_COMPRESSED_MAX) return 0;
    return (c->data[byte_idx] >> bit_idx) & 1;
}

/* ---- Public API ------------------------------------------------------- */

void tfs_init(tfs_state_t *fs) {
    if (!fs) return;
    memset(fs, 0, sizeof(*fs));

    /* Superblock */
    fs->magic[0] = TFS_MAGIC_TRIT_0;
    fs->magic[1] = TFS_MAGIC_TRIT_1;
    fs->magic[2] = TFS_MAGIC_TRIT_2;
    fs->version = TFS_VERSION;
    fs->total_blocks = TFS_MAX_BLOCKS;
    fs->free_blocks = TFS_MAX_BLOCKS;
    fs->total_files = 0;

    /* Mark all blocks free */
    for (int i = 0; i < TFS_MAX_BLOCKS; i++)
        fs->block_free[i] = 1;

    /* Clear all inodes */
    for (int i = 0; i < TFS_MAX_FILES; i++)
        fs->inodes[i].valid = 0;

    fs->root_dir_count = 0;
    fs->initialized = 1;
}

trit tfs_guardian_compute(const trit *data, int count) {
    trit g = TRIT_UNKNOWN;
    for (int i = 0; i < count; i++)
        g = trit_xor3(g, data[i]);
    return g;
}

int tfs_huffman_encode(tfs_compressed_block_t *out,
                       const trit *trits, int count) {
    if (!out || !trits || count <= 0)
        return -1;

    memset(out, 0, sizeof(*out));
    out->original_trits = count;

    int pos = 0;
    for (int i = 0; i < count; i++) {
        switch (trits[i]) {
            case TRIT_UNKNOWN:  /* 0 → '0' (1 bit) */
                set_bit(out, pos++, 0);
                break;
            case TRIT_TRUE:     /* +1 → '10' (2 bits) */
                set_bit(out, pos++, 1);
                set_bit(out, pos++, 0);
                break;
            case TRIT_FALSE:    /* -1 → '11' (2 bits) */
                set_bit(out, pos++, 1);
                set_bit(out, pos++, 1);
                break;
            default:
                set_bit(out, pos++, 0);
                break;
        }
        if (pos > TFS_COMPRESSED_MAX * 8)
            return -1;
    }

    out->bit_count = pos;
    out->byte_count = (pos + 7) / 8;
    out->guardian = tfs_guardian_compute(trits, count);
    return pos;
}

int tfs_huffman_decode(trit *trits, int max_trits,
                       const tfs_compressed_block_t *comp) {
    if (!trits || !comp || comp->bit_count <= 0)
        return -1;

    int pos = 0;
    int count = 0;

    while (pos < comp->bit_count && count < max_trits &&
           count < comp->original_trits) {
        int bit = get_bit(comp, pos++);
        if (bit == 0) {
            trits[count++] = TRIT_UNKNOWN;
        } else {
            if (pos >= comp->bit_count) break;
            int bit2 = get_bit(comp, pos++);
            if (bit2 == 0)
                trits[count++] = TRIT_TRUE;
            else
                trits[count++] = TRIT_FALSE;
        }
    }

    return count;
}

tfs_freq_t tfs_frequency(const trit *trits, int count) {
    tfs_freq_t f = {0, 0, 0, 0};
    for (int i = 0; i < count; i++) {
        switch (trits[i]) {
            case TRIT_FALSE:   f.freq_neg++;  break;
            case TRIT_UNKNOWN: f.freq_zero++; break;
            case TRIT_TRUE:    f.freq_pos++;  break;
            default: break;
        }
    }
    f.total = count;
    return f;
}

int tfs_open(tfs_state_t *fs, const char *name, tfs_mode_t mode, tfs_fd_t *fd) {
    if (!fs || !name || !fd || !fs->initialized)
        return -1;

    int inode_idx = find_inode(fs, name);

    if (mode == TFS_MODE_READ) {
        /* File must exist */
        if (inode_idx < 0) return -1;
    } else {
        /* Write or Append — create if not exists */
        if (inode_idx < 0) {
            inode_idx = alloc_inode(fs);
            if (inode_idx < 0) return -1;

            tfs_inode_t *inode = &fs->inodes[inode_idx];
            memset(inode, 0, sizeof(*inode));
            strncpy(inode->name, name, TFS_MAX_FILENAME - 1);
            inode->name[TFS_MAX_FILENAME - 1] = '\0';
            inode->valid = 1;
            inode->mode = mode;
            fs->total_files++;

            /* Add to root directory */
            if (fs->root_dir_count < TFS_MAX_DIR_ENTRIES) {
                tfs_dirent_t *de = &fs->root_dir[fs->root_dir_count++];
                strncpy(de->name, name, TFS_MAX_FILENAME - 1);
                de->name[TFS_MAX_FILENAME - 1] = '\0';
                de->inode_idx = inode_idx;
                de->priority = TRIT_UNKNOWN; /* Leaf in trit-tree */
            }
        }

        if (mode == TFS_MODE_WRITE) {
            /* Truncate: free existing blocks */
            tfs_inode_t *inode = &fs->inodes[inode_idx];
            for (int i = 0; i < inode->block_count; i++) {
                int bidx = inode->blocks[i];
                if (bidx >= 0 && bidx < fs->total_blocks) {
                    fs->block_free[bidx] = 1;
                    fs->free_blocks++;
                    memset(&fs->blocks[bidx], 0, sizeof(tfs_block_t));
                }
            }
            inode->block_count = 0;
            inode->size_trits = 0;
        }
    }

    /* Set up file descriptor */
    fd->inode_idx = inode_idx;
    fd->mode = mode;
    fd->valid = 1;
    fd->cursor_trit = (mode == TFS_MODE_APPEND)
                      ? fs->inodes[inode_idx].size_trits
                      : 0;

    fs->inodes[inode_idx].open_count++;
    return 0;
}

int tfs_write(tfs_state_t *fs, tfs_fd_t *fd, const trit *trits, int count) {
    if (!fs || !fd || !trits || count <= 0 || !fd->valid)
        return -1;
    if (fd->mode == TFS_MODE_READ)
        return -1;

    tfs_inode_t *inode = &fs->inodes[fd->inode_idx];
    int written = 0;

    while (written < count) {
        /* Find or allocate a block for the current cursor position */
        int block_idx_in_file = fd->cursor_trit / TFS_BLOCK_TRITS;
        int offset_in_block   = fd->cursor_trit % TFS_BLOCK_TRITS;

        if (block_idx_in_file >= TFS_BLOCKS_PER_FILE)
            break;  /* File full */

        /* Allocate block if needed */
        if (block_idx_in_file >= inode->block_count) {
            int bidx = find_free_block(fs);
            if (bidx < 0) break;  /* No free blocks */

            fs->block_free[bidx] = 0;
            fs->free_blocks--;
            inode->blocks[inode->block_count++] = bidx;

            /* Initialize block to Unknown */
            tfs_block_t *blk = &fs->blocks[bidx];
            memset(blk, 0, sizeof(*blk));
            for (int i = 0; i < TFS_BLOCK_TRITS; i++)
                blk->data[i] = TRIT_UNKNOWN;
        }

        int bidx = inode->blocks[block_idx_in_file];
        tfs_block_t *blk = &fs->blocks[bidx];

        /* Write trits into block */
        int space = TFS_BLOCK_TRITS - offset_in_block;
        int to_write = (count - written < space) ? (count - written) : space;

        memcpy(&blk->data[offset_in_block], &trits[written],
               (size_t)to_write * sizeof(trit));

        /* Update block metadata */
        int new_used = offset_in_block + to_write;
        if (new_used > blk->used_trits)
            blk->used_trits = new_used;
        blk->guardian = tfs_guardian_compute(blk->data, blk->used_trits);

        written += to_write;
        fd->cursor_trit += to_write;
    }

    /* Update inode size */
    if (fd->cursor_trit > inode->size_trits)
        inode->size_trits = fd->cursor_trit;

    inode->write_count++;
    fs->total_writes++;

    return written;
}

int tfs_read(tfs_state_t *fs, tfs_fd_t *fd, trit *trits, int max_trits) {
    if (!fs || !fd || !trits || max_trits <= 0 || !fd->valid)
        return -1;

    tfs_inode_t *inode = &fs->inodes[fd->inode_idx];
    int readable = inode->size_trits - fd->cursor_trit;
    if (readable <= 0) return 0;  /* EOF */

    int to_read = (max_trits < readable) ? max_trits : readable;
    int total_read = 0;

    while (total_read < to_read) {
        int block_idx_in_file = fd->cursor_trit / TFS_BLOCK_TRITS;
        int offset_in_block   = fd->cursor_trit % TFS_BLOCK_TRITS;

        if (block_idx_in_file >= inode->block_count)
            break;

        int bidx = inode->blocks[block_idx_in_file];
        tfs_block_t *blk = &fs->blocks[bidx];

        /* Validate guardian before reading */
        trit expected = tfs_guardian_compute(blk->data, blk->used_trits);
        if (expected != blk->guardian) {
            fs->guardian_failures++;
            /* Continue anyway — data may be partially valid */
        }
        fs->guardian_checks++;

        int avail = blk->used_trits - offset_in_block;
        if (avail <= 0) break;

        int n = (to_read - total_read < avail) ? (to_read - total_read) : avail;
        memcpy(&trits[total_read], &blk->data[offset_in_block],
               (size_t)n * sizeof(trit));

        total_read += n;
        fd->cursor_trit += n;
    }

    inode->read_count++;
    fs->total_reads++;

    return total_read;
}

int tfs_close(tfs_state_t *fs, tfs_fd_t *fd) {
    if (!fs || !fd || !fd->valid)
        return -1;

    fs->inodes[fd->inode_idx].open_count--;
    fd->valid = 0;
    return 0;
}

int tfs_sync(tfs_state_t *fs, tfs_fd_t *fd) {
    if (!fs || !fd || !fd->valid)
        return -1;

    tfs_inode_t *inode = &fs->inodes[fd->inode_idx];
    int validated = 0;

    for (int i = 0; i < inode->block_count; i++) {
        int bidx = inode->blocks[i];
        tfs_block_t *blk = &fs->blocks[bidx];

        /* Recompute and verify guardian */
        trit expected = tfs_guardian_compute(blk->data, blk->used_trits);
        if (expected != blk->guardian) {
            fs->guardian_failures++;
            blk->guardian = expected;  /* Fix it */
        }
        fs->guardian_checks++;
        validated++;
    }

    return validated;
}

int tfs_compress(tfs_state_t *fs, const char *name) {
    if (!fs || !name) return -1;

    int inode_idx = find_inode(fs, name);
    if (inode_idx < 0) return -1;

    tfs_inode_t *inode = &fs->inodes[inode_idx];
    int compressed_count = 0;

    for (int i = 0; i < inode->block_count; i++) {
        int bidx = inode->blocks[i];
        tfs_block_t *blk = &fs->blocks[bidx];

        if (blk->used_trits > 0) {
            int bits = tfs_huffman_encode(&blk->comp,
                                          blk->data, blk->used_trits);
            if (bits > 0) {
                blk->compressed = 1;
                compressed_count++;
            }
        }
    }

    fs->total_compressions += compressed_count;
    return compressed_count;
}

int tfs_unlink(tfs_state_t *fs, const char *name) {
    if (!fs || !name) return -1;

    int inode_idx = find_inode(fs, name);
    if (inode_idx < 0) return -1;

    tfs_inode_t *inode = &fs->inodes[inode_idx];
    if (inode->open_count > 0)
        return -1;  /* Can't delete while open */

    /* Free blocks */
    for (int i = 0; i < inode->block_count; i++) {
        int bidx = inode->blocks[i];
        if (bidx >= 0 && bidx < fs->total_blocks) {
            fs->block_free[bidx] = 1;
            fs->free_blocks++;
            memset(&fs->blocks[bidx], 0, sizeof(tfs_block_t));
        }
    }

    /* Remove from directory */
    for (int i = 0; i < fs->root_dir_count; i++) {
        if (fs->root_dir[i].inode_idx == inode_idx) {
            /* Shift entries down */
            for (int j = i; j < fs->root_dir_count - 1; j++)
                fs->root_dir[j] = fs->root_dir[j + 1];
            fs->root_dir_count--;
            break;
        }
    }

    /* Clear inode */
    memset(inode, 0, sizeof(*inode));
    fs->total_files--;

    return 0;
}

void tfs_get_stats(const tfs_state_t *fs, int *files, int *free_blocks,
                   int *reads, int *writes, int *compressions) {
    if (!fs) return;
    if (files)        *files = fs->total_files;
    if (free_blocks)  *free_blocks = fs->free_blocks;
    if (reads)        *reads = fs->total_reads;
    if (writes)       *writes = fs->total_writes;
    if (compressions) *compressions = fs->total_compressions;
}

int tfs_density_gain_x100(void) {
    return TFS_DENSITY_GAIN_X100;
}

int tfs_area_reduction_x100(void) {
    return TFS_AREA_REDUCTION_X100;
}
