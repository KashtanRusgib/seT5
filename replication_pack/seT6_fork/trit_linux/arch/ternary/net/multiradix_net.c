/**
 * @file multiradix_net.c
 * @brief Trit Linux — Multi-Radix Network Driver
 *
 * Network driver using balanced ternary packet encoding with
 * multi-radix FFT for efficient signal processing. Inspired by
 * Groq G300's radix-4 network topology.
 *
 * Packet format:
 *   Header:  6 trits (src addr) + 6 trits (dst addr) + 3 trits (type)
 *   Payload: up to 32 trits (one trit2_reg32 register)
 *   CRC:     3 trits (ternary checksum)
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "asm/trit_types.h"
#include "set6/trit.h"
#include "set6/trit_emu.h"
#include "set6/multiradix.h"
#include <string.h>
#include <stdio.h>

/* ---- Packet format ---------------------------------------------------- */

#define NET_ADDR_TRITS     6
#define NET_TYPE_TRITS     3
#define NET_PAYLOAD_TRITS  32     /* one register width */
#define NET_CRC_TRITS      3
#define NET_HEADER_TRITS   (NET_ADDR_TRITS * 2 + NET_TYPE_TRITS)
#define NET_MAX_PACKETS    64

/** Packet types */
#define NET_TYPE_DATA      0
#define NET_TYPE_ACK       1
#define NET_TYPE_FFT       2      /* FFT-encoded payload */

/** Ternary network packet */
typedef struct {
    trit src_addr[NET_ADDR_TRITS];
    trit dst_addr[NET_ADDR_TRITS];
    int  pkt_type;
    trit payload[NET_PAYLOAD_TRITS];
    int  payload_len;
    trit crc[NET_CRC_TRITS];
    int  valid;
} trit_net_packet_t;

/* ---- Packet buffer (ring queue) --------------------------------------- */

typedef struct {
    trit_net_packet_t packets[NET_MAX_PACKETS];
    int               head;
    int               tail;
    int               count;
} trit_net_queue_t;

/** Network driver state */
typedef struct {
    trit_net_queue_t    tx_queue;     /**< Transmit queue */
    trit_net_queue_t    rx_queue;     /**< Receive queue */
    multiradix_state_t  mr;          /**< Multi-radix engine for FFT */
    trit                local_addr[NET_ADDR_TRITS]; /**< Our address */
    int                 tx_count;    /**< Total packets sent */
    int                 rx_count;    /**< Total packets received */
    int                 crc_errors;  /**< CRC mismatches */
    int                 initialized; /**< 1 = ready */
} trit_net_driver_t;

/* ---- Global driver instance ------------------------------------------ */

static trit_net_driver_t net_driver;

/* ---- CRC computation -------------------------------------------------- */

/** Compute 3-trit CRC over a trit array */
static void trit_crc_compute(const trit *data, int len, trit crc[NET_CRC_TRITS]) {
    int accum[NET_CRC_TRITS] = {0, 0, 0};
    for (int i = 0; i < len; i++) {
        accum[i % NET_CRC_TRITS] += data[i];
    }
    /* Reduce to balanced ternary range */
    for (int i = 0; i < NET_CRC_TRITS; i++) {
        int v = ((accum[i] % 3) + 3) % 3;
        if (v == 0)      crc[i] = 0;
        else if (v == 1) crc[i] = 1;
        else             crc[i] = -1;
    }
}

/** Verify CRC matches */
static int trit_crc_verify(const trit *data, int len, const trit crc[NET_CRC_TRITS]) {
    trit expected[NET_CRC_TRITS];
    trit_crc_compute(data, len, expected);
    for (int i = 0; i < NET_CRC_TRITS; i++) {
        if (expected[i] != crc[i]) return 0;
    }
    return 1;
}

/* ---- Queue operations ------------------------------------------------- */

static void queue_init(trit_net_queue_t *q) {
    memset(q, 0, sizeof(*q));
}

static int queue_push(trit_net_queue_t *q, const trit_net_packet_t *pkt) {
    if (q->count >= NET_MAX_PACKETS) return -1;
    q->packets[q->tail] = *pkt;
    q->tail = (q->tail + 1) % NET_MAX_PACKETS;
    q->count++;
    return 0;
}

static int queue_pop(trit_net_queue_t *q, trit_net_packet_t *pkt) {
    if (q->count == 0) return -1;
    *pkt = q->packets[q->head];
    q->head = (q->head + 1) % NET_MAX_PACKETS;
    q->count--;
    return 0;
}

/* ---- Driver API ------------------------------------------------------- */

/** Initialize the multi-radix network driver */
int trit_net_init(const trit local_addr[NET_ADDR_TRITS]) {
    memset(&net_driver, 0, sizeof(net_driver));
    queue_init(&net_driver.tx_queue);
    queue_init(&net_driver.rx_queue);
    multiradix_init(&net_driver.mr);
    memcpy(net_driver.local_addr, local_addr, sizeof(trit) * NET_ADDR_TRITS);
    net_driver.initialized = 1;
    return 0;
}

/** Build a packet */
void trit_net_build_packet(trit_net_packet_t *pkt,
                           const trit src[NET_ADDR_TRITS],
                           const trit dst[NET_ADDR_TRITS],
                           int pkt_type,
                           const trit *payload, int payload_len) {
    memset(pkt, 0, sizeof(*pkt));
    memcpy(pkt->src_addr, src, sizeof(trit) * NET_ADDR_TRITS);
    memcpy(pkt->dst_addr, dst, sizeof(trit) * NET_ADDR_TRITS);
    pkt->pkt_type = pkt_type;
    if (payload && payload_len > 0) {
        if (payload_len > NET_PAYLOAD_TRITS) payload_len = NET_PAYLOAD_TRITS;
        memcpy(pkt->payload, payload, sizeof(trit) * payload_len);
    }
    pkt->payload_len = payload_len;
    trit_crc_compute(pkt->payload, pkt->payload_len, pkt->crc);
    pkt->valid = 1;
}

/** Send a packet (enqueue for transmission) */
int trit_net_send(const trit dst[NET_ADDR_TRITS], int pkt_type,
                  const trit *payload, int payload_len) {
    if (!net_driver.initialized) return -1;

    trit_net_packet_t pkt;
    trit_net_build_packet(&pkt, net_driver.local_addr, dst,
                          pkt_type, payload, payload_len);

    int result = queue_push(&net_driver.tx_queue, &pkt);
    if (result == 0) net_driver.tx_count++;
    return result;
}

/** Receive a packet (dequeue from RX buffer) */
int trit_net_recv(trit_net_packet_t *pkt) {
    if (!net_driver.initialized) return -1;
    return queue_pop(&net_driver.rx_queue, pkt);
}

/** Simulate loopback: move TX packets matching our address to RX */
int trit_net_loopback(void) {
    if (!net_driver.initialized) return -1;

    int looped = 0;
    trit_net_packet_t pkt;
    while (queue_pop(&net_driver.tx_queue, &pkt) == 0) {
        /* Check if destination matches our address */
        int match = 1;
        for (int i = 0; i < NET_ADDR_TRITS; i++) {
            if (pkt.dst_addr[i] != net_driver.local_addr[i]) {
                match = 0;
                break;
            }
        }
        if (match) {
            /* Verify CRC before accepting */
            if (trit_crc_verify(pkt.payload, pkt.payload_len, pkt.crc)) {
                queue_push(&net_driver.rx_queue, &pkt);
                net_driver.rx_count++;
                looped++;
            } else {
                net_driver.crc_errors++;
            }
        }
    }
    return looped;
}

/** FFT-encode a payload using multi-radix engine */
int trit_net_fft_encode(trit *payload, int len) {
    if (!net_driver.initialized || len <= 0) return -1;

    /* Load payload into MR register 0 */
    trit2_reg32 reg = trit2_reg32_splat(TRIT2_UNKNOWN);
    for (int i = 0; i < len && i < 32; i++) {
        trit2 t = trit2_encode(payload[i]);
        trit2_reg32_set(&reg, i, t);
    }
    net_driver.mr.regs[0] = reg;

    /* Apply FFT step: reg0 → reg1 */
    fft_step(&net_driver.mr, 0, 1, 1);

    /* Read back from reg1 */
    for (int i = 0; i < len && i < 32; i++) {
        payload[i] = (trit)trit2_decode(trit2_reg32_get(&net_driver.mr.regs[1], i));
    }

    return 0;
}

/** Compute dot product between two payloads (similarity metric) */
int trit_net_dot(const trit *a, const trit *b, int len) {
    int sum = 0;
    for (int i = 0; i < len; i++) {
        sum += a[i] * b[i];
    }
    return sum;
}

/** Get driver statistics */
void trit_net_stats(int *tx, int *rx, int *errors) {
    if (tx) *tx = net_driver.tx_count;
    if (rx) *rx = net_driver.rx_count;
    if (errors) *errors = net_driver.crc_errors;
}

/** Check if driver is initialized */
int trit_net_is_ready(void) {
    return net_driver.initialized;
}
