/**
 * @file tipc.h
 * @brief seT5 Ternary-Native Inter-Process Communication (T-IPC) Protocol
 *
 * Enables trit-compressed message exchange between user-space modules
 * across the STT-MRAM memory interface.  Uses Balanced Ternary Huffman
 * Coding for ~40% density gain over binary IPC.
 *
 * Features:
 *   - Adaptive Huffman compression (short codes for frequent '0'/Unknown)
 *   - Guardian Trit integrity checksums
 *   - Radix validation (quarantine binary-only payloads)
 *   - In-memory differential updates via MEM_XOR_T
 *
 * Interfaces through existing IPC/MMU abstractions — zero kernel changes.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET5_TIPC_H
#define SET5_TIPC_H

#include "set5/trit.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ========================================================= */

#define TIPC_MAX_TRITS        512      /* Max trits per message            */
#define TIPC_MAX_COMPRESSED   128      /* Max compressed bytes per message */
#define TIPC_MAX_ENDPOINTS    16       /* Max T-IPC endpoints              */
#define TIPC_TRYTE_TRITS      9        /* Trits per tryte                  */
#define TIPC_TRYTE_BITS       14       /* Compressed bits per tryte (max)  */
#define TIPC_GUARDIAN_OK      0
#define TIPC_GUARDIAN_FAIL    (-1)

/** Huffman codes for balanced ternary:
 *  0 (Unknown) → '0' (1 bit)     — most frequent in sparse data
 *  +1 (True)   → '10' (2 bits)
 *  -1 (False)  → '11' (2 bits)
 */
#define TIPC_HUFF_ZERO_BITS   1
#define TIPC_HUFF_POS_BITS    2
#define TIPC_HUFF_NEG_BITS    2

/* ==== Command IDs ======================================================= */

#define TIPC_CMD_SEND         0x10     /* Compress and send trit-message   */
#define TIPC_CMD_RECV         0x11     /* Receive and decompress           */
#define TIPC_CMD_XOR_DIFF     0x12     /* Differential update (in-memory)  */
#define TIPC_CMD_GUARD        0x13     /* Validate radix purity            */

/* ==== Types ============================================================= */

/** Message priority (maps to trit) */
typedef enum {
    TIPC_PRIO_LOW    = -1,
    TIPC_PRIO_MEDIUM =  0,
    TIPC_PRIO_HIGH   =  1
} tipc_priority_t;

/** Compressed message buffer */
typedef struct {
    uint8_t  data[TIPC_MAX_COMPRESSED];
    int      bit_count;        /* Total bits in compressed stream */
    int      byte_count;       /* Bytes used in data[]            */
    int      original_trits;   /* Original trit count before compression */
} tipc_compressed_t;

/** T-IPC message */
typedef struct {
    trit             trits[TIPC_MAX_TRITS];
    int              count;
    tipc_priority_t  priority;
    trit             guardian;     /* XOR checksum of all trits */
    int              compressed;   /* 1 if currently compressed */
} tipc_message_t;

/** T-IPC endpoint */
typedef struct {
    int              id;
    int              active;
    tipc_message_t   inbox;        /* Last received message */
    int              msg_count;    /* Total messages received */
    int              guard_fails;  /* Guardian validation failures */
} tipc_endpoint_t;

/** T-IPC channel (pair of endpoints) */
typedef struct {
    tipc_endpoint_t  endpoints[TIPC_MAX_ENDPOINTS];
    int              active_count;

    /* Statistics */
    int              total_sent;
    int              total_received;
    int              total_compressed_bits;
    int              total_raw_trits;
    int              radix_violations;
} tipc_channel_t;

/** Huffman frequency table */
typedef struct {
    int freq_neg;    /* Count of -1 trits */
    int freq_zero;   /* Count of  0 trits */
    int freq_pos;    /* Count of +1 trits */
} tipc_freq_t;

/* ==== API ================================================================ */

/**
 * @brief Initialize a T-IPC channel.
 */
void tipc_channel_init(tipc_channel_t *ch);

/**
 * @brief Create an endpoint in the channel.
 * @return Endpoint ID (≥0) or -1 on error.
 */
int tipc_endpoint_create(tipc_channel_t *ch);

/**
 * @brief Compute the Guardian Trit (XOR checksum) of a trit buffer.
 *
 * Guardian = running balanced-ternary addition of all trits.
 * A valid message should have a predictable guardian value.
 *
 * @param trits  Input trit buffer.
 * @param count  Number of trits.
 * @return Guardian trit value.
 */
trit tipc_guardian_compute(const trit *trits, int count);

/**
 * @brief Validate a message's Guardian Trit.
 * @return TIPC_GUARDIAN_OK or TIPC_GUARDIAN_FAIL.
 */
int tipc_guardian_validate(const tipc_message_t *msg);

/**
 * @brief Compress a trit buffer using Balanced Ternary Huffman.
 *
 * @param out    Compressed output.
 * @param trits  Input trit buffer.
 * @param count  Number of trits.
 * @return Number of compressed bits, or -1 on error.
 */
int tipc_compress(tipc_compressed_t *out, const trit *trits, int count);

/**
 * @brief Decompress a Huffman-encoded buffer back to trits.
 *
 * @param trits     Output trit buffer.
 * @param max_trits Maximum trits to decompress.
 * @param comp      Compressed input.
 * @return Number of trits recovered, or -1 on error.
 */
int tipc_decompress(trit *trits, int max_trits, const tipc_compressed_t *comp);

/**
 * @brief TIPC_SEND — Compress and send a trit-message to an endpoint.
 *
 * @param ch       Channel.
 * @param dst_id   Destination endpoint ID.
 * @param trits    Message trits.
 * @param count    Number of trits.
 * @param priority Message priority.
 * @return 0 on success, -1 on error.
 */
int tipc_send(tipc_channel_t *ch, int dst_id,
              const trit *trits, int count, tipc_priority_t priority);

/**
 * @brief TIPC_RECV — Receive and decompress from an endpoint's inbox.
 *
 * @param ch       Channel.
 * @param ep_id    Endpoint ID.
 * @param trits    Output trit buffer.
 * @param max_trits Buffer capacity.
 * @return Number of trits received, or -1 on error / empty.
 */
int tipc_recv(tipc_channel_t *ch, int ep_id, trit *trits, int max_trits);

/**
 * @brief TIPC_XOR_DIFF — Apply differential XOR update.
 *
 * XOR a delta buffer against a message in-place, simulating
 * zero-CPU-cycle in-memory differential updates.
 *
 * @param msg    Message to update.
 * @param delta  Delta trit buffer.
 * @param count  Number of delta trits.
 * @return 0 on success, -1 on error.
 */
int tipc_xor_diff(tipc_message_t *msg, const trit *delta, int count);

/**
 * @brief TIPC_GUARD — Validate radix purity of a byte buffer.
 *
 * Checks whether a buffer contains valid ternary-encoded data.
 * Binary-only (non-ternary) payloads are flagged as violations.
 *
 * @param data  Input byte buffer.
 * @param len   Buffer length.
 * @return 0 if ternary-pure, 1 if binary violation detected.
 */
int tipc_radix_guard(const uint8_t *data, int len);

/**
 * @brief Count trit frequencies in a buffer.
 */
tipc_freq_t tipc_frequency(const trit *trits, int count);

/**
 * @brief Compute compression ratio (×1000 for precision).
 *
 * ratio = compressed_bits * 1000 / (original_trits * 1585)
 * Lower is better.
 *
 * @param comp Compressed buffer.
 * @return Ratio ×1000, or -1 if invalid.
 */
int tipc_compression_ratio(const tipc_compressed_t *comp);

#ifdef __cplusplus
}
#endif

#endif /* SET5_TIPC_H */
