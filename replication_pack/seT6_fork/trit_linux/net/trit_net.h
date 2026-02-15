/**
 * @file trit_net.h
 * @brief Trit Linux — Ternary-Optimized Networking Stack Header
 *
 * Defines the T-Net protocol: a lightweight ternary UDP/TCP analog
 * using trit-compressed headers for ~1.58x efficiency. Includes a
 * Kleene state firewall, virtual Ethernet driver, and user-space
 * tools interface (trit-ping, trit-curl).
 *
 * Enhancement 2 from LOGICAL_ENHANCEMENTS_FOR_TRIT_LINUX.md:
 *   "Ternary-Optimized Networking Stack"
 *
 * Key features:
 *   - T-Net Protocol: 42-trit addresses, trit-compressed headers
 *   - Kleene firewall: -1 deny, 0 inspect, +1 allow
 *   - MEM_XOR_T checksums from STT-MRAM
 *   - Virtual Ethernet driver (loopback + simulated latency)
 *   - ARP-like trit address resolution
 *   - Connection tracking with ternary states
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef TRIT_LINUX_TRIT_NET_H
#define TRIT_LINUX_TRIT_NET_H

#include "set6/trit.h"
#include "set6/tipc.h"
#include "set6/stt_mram.h"
#include "set6/multiradix.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ========================================================= */

#define TNET_ADDR_TRITS      12    /* 42-trit address (3^12 = 531441 nodes) */
#define TNET_PORT_TRITS      6     /* 3^6 = 729 ports                       */
#define TNET_MAX_PAYLOAD     256   /* Max payload trits per packet           */
#define TNET_HEADER_TRITS    36    /* src(12) + dst(12) + sport(6) + dport(6)*/
#define TNET_CHECKSUM_TRITS  6     /* XOR-based trit checksum               */
#define TNET_MAX_CONNECTIONS 16    /* Max simultaneous connections           */
#define TNET_MAX_FIREWALL    32    /* Max firewall rules                    */
#define TNET_ARP_CACHE_SIZE  16    /* ARP cache entries                     */
#define TNET_RX_QUEUE_SIZE   32    /* Receive queue depth                   */
#define TNET_TX_QUEUE_SIZE   32    /* Transmit queue depth                  */

/* Protocol types (balanced ternary encoded) */
#define TNET_PROTO_DATA      0     /* Raw data transfer                     */
#define TNET_PROTO_ACK       1     /* Acknowledgement                       */
#define TNET_PROTO_PING      2     /* Echo request                          */
#define TNET_PROTO_PONG      3     /* Echo reply                            */
#define TNET_PROTO_ARP_REQ   4     /* Address resolution request            */
#define TNET_PROTO_ARP_REPLY 5     /* Address resolution reply              */
#define TNET_PROTO_FIN       6     /* Connection close                      */

/* Error codes */
#define TNET_OK              0
#define TNET_ERR_INIT       (-1)
#define TNET_ERR_FULL       (-2)
#define TNET_ERR_NOCONN     (-3)
#define TNET_ERR_DENIED     (-4)   /* Firewall denied */
#define TNET_ERR_CHECKSUM   (-5)
#define TNET_ERR_TIMEOUT    (-6)
#define TNET_ERR_BADADDR    (-7)

/* ==== Types ============================================================= */

/**
 * @brief T-Net address: 12 balanced trits (3^12 = 531441 unique addresses).
 */
typedef struct {
    trit digits[TNET_ADDR_TRITS];
} tnet_addr_t;

/**
 * @brief T-Net port: 6 balanced trits (3^6 = 729 ports).
 */
typedef struct {
    trit digits[TNET_PORT_TRITS];
} tnet_port_t;

/**
 * @brief T-Net packet header.
 *
 * Contains source/destination addresses and ports, protocol type,
 * payload length, and a 6-trit XOR checksum.
 */
typedef struct {
    tnet_addr_t src_addr;                /**< Source address (12 trits)     */
    tnet_addr_t dst_addr;                /**< Destination address (12 trits)*/
    tnet_port_t src_port;                /**< Source port (6 trits)         */
    tnet_port_t dst_port;                /**< Destination port (6 trits)    */
    int         protocol;                /**< Protocol type                 */
    int         payload_len;             /**< Payload length in trits       */
    trit        checksum[TNET_CHECKSUM_TRITS]; /**< XOR-based checksum     */
    int         ttl;                     /**< Time-to-live (hop count)      */
    int         seq_num;                 /**< Sequence number               */
} tnet_header_t;

/**
 * @brief T-Net packet (header + payload).
 */
typedef struct {
    tnet_header_t header;
    trit          payload[TNET_MAX_PAYLOAD];
    int           valid;                 /**< 1 = valid, 0 = invalid        */
} tnet_packet_t;

/**
 * @brief Kleene firewall rule.
 *
 * Uses ternary logic for packet filtering:
 *   +1 (True)    = ALLOW
 *    0 (Unknown) = INSPECT (log and pass)
 *   -1 (False)   = DENY
 */
typedef struct {
    tnet_addr_t src_mask;    /**< Source address mask (0=wildcard)          */
    tnet_port_t port_mask;   /**< Port mask (0=wildcard)                   */
    int         protocol;    /**< Protocol to match (-1=any)               */
    trit        action;      /**< +1=allow, 0=inspect, -1=deny             */
    int         match_count; /**< How many packets matched this rule       */
    int         active;      /**< 1 = rule is active                       */
} tnet_firewall_rule_t;

/**
 * @brief Connection state (ternary FSM).
 *
 * Tracks active connections with trit-state:
 *   +1 = ESTABLISHED
 *    0 = HALF_OPEN (SYN sent, no ACK)
 *   -1 = CLOSED
 */
typedef struct {
    tnet_addr_t remote_addr; /**< Remote peer address                      */
    tnet_port_t local_port;  /**< Our port                                 */
    tnet_port_t remote_port; /**< Peer port                                */
    trit        state;       /**< +1=established, 0=half-open, -1=closed   */
    int         tx_seq;      /**< Next TX sequence number                  */
    int         rx_seq;      /**< Expected RX sequence number              */
    int         tx_count;    /**< Packets sent                             */
    int         rx_count;    /**< Packets received                         */
} tnet_connection_t;

/**
 * @brief ARP (Address Resolution Protocol) cache entry.
 */
typedef struct {
    tnet_addr_t net_addr;    /**< Network (T-Net) address                  */
    int         hw_id;       /**< Hardware/MAC-like identifier             */
    int         valid;       /**< 1 = entry is valid                       */
    int         age;         /**< Ticks since last use (for eviction)      */
} tnet_arp_entry_t;

/**
 * @brief T-Net stack state.
 *
 * Master state for the ternary networking stack, containing the
 * local address, firewall rules, connection table, ARP cache,
 * and packet queues.
 */
typedef struct {
    tnet_addr_t          local_addr;        /**< Our network address           */
    int                  initialized;       /**< 1 = stack is ready            */

    /* Firewall */
    tnet_firewall_rule_t firewall[TNET_MAX_FIREWALL];
    int                  fw_rule_count;     /**< Active firewall rules         */
    int                  fw_denied;         /**< Total packets denied          */
    int                  fw_inspected;      /**< Total packets inspected       */
    int                  fw_allowed;        /**< Total packets allowed         */

    /* Connections */
    tnet_connection_t    connections[TNET_MAX_CONNECTIONS];
    int                  conn_count;        /**< Active connections            */

    /* ARP cache */
    tnet_arp_entry_t     arp_cache[TNET_ARP_CACHE_SIZE];
    int                  arp_count;         /**< Valid ARP entries             */

    /* Packet queues */
    tnet_packet_t        tx_queue[TNET_TX_QUEUE_SIZE];
    int                  tx_head, tx_tail, tx_count;
    tnet_packet_t        rx_queue[TNET_RX_QUEUE_SIZE];
    int                  rx_head, rx_tail, rx_count;

    /* Multi-radix engine for encryption/checksums */
    multiradix_state_t   mr;

    /* Statistics */
    int                  total_tx;          /**< Total packets transmitted     */
    int                  total_rx;          /**< Total packets received        */
    int                  checksum_errors;   /**< Checksum mismatches           */
    int                  seq_next;          /**< Next global sequence number   */
} tnet_stack_t;

/* ==== Initialization ==================================================== */

/**
 * @brief Initialize the T-Net stack.
 * @param stack  Stack state to initialize.
 * @param addr   Local network address (12 trits).
 * @return TNET_OK on success.
 */
int tnet_init(tnet_stack_t *stack, const tnet_addr_t *addr);

/* ==== Address Utilities ================================================= */

/** Set address from integer (for convenience) */
void tnet_addr_from_int(tnet_addr_t *addr, int value);

/** Convert address to integer */
int tnet_addr_to_int(const tnet_addr_t *addr);

/** Compare two addresses */
int tnet_addr_equal(const tnet_addr_t *a, const tnet_addr_t *b);

/** Set port from integer */
void tnet_port_from_int(tnet_port_t *port, int value);

/** Convert port to integer */
int tnet_port_to_int(const tnet_port_t *port);

/* ==== Packet Operations ================================================= */

/** Build a T-Net packet with header and payload */
int tnet_build_packet(tnet_packet_t *pkt,
                      const tnet_addr_t *src, const tnet_addr_t *dst,
                      const tnet_port_t *sport, const tnet_port_t *dport,
                      int protocol, const trit *payload, int len);

/** Compute XOR checksum over packet payload */
void tnet_checksum_compute(trit *checksum, const trit *data, int len);

/** Verify packet checksum */
int tnet_checksum_verify(const tnet_packet_t *pkt);

/* ==== Send/Receive ====================================================== */

/** Send a packet (enqueue to TX) */
int tnet_send(tnet_stack_t *stack, const tnet_addr_t *dst,
              const tnet_port_t *dport, int protocol,
              const trit *payload, int len);

/** Receive a packet (dequeue from RX) */
int tnet_recv(tnet_stack_t *stack, tnet_packet_t *pkt);

/** Loopback: move TX packets addressed to us into RX queue */
int tnet_loopback(tnet_stack_t *stack);

/* ==== Firewall ========================================================== */

/** Add a firewall rule */
int tnet_fw_add_rule(tnet_stack_t *stack, const tnet_addr_t *src_mask,
                     const tnet_port_t *port_mask, int protocol, trit action);

/** Evaluate a packet against the firewall (returns action trit) */
trit tnet_fw_evaluate(tnet_stack_t *stack, const tnet_packet_t *pkt);

/** Get firewall statistics */
void tnet_fw_stats(const tnet_stack_t *stack,
                   int *denied, int *inspected, int *allowed);

/* ==== Connection Management ============================================= */

/** Open a connection to a remote peer */
int tnet_connect(tnet_stack_t *stack, const tnet_addr_t *remote,
                 const tnet_port_t *local_port, const tnet_port_t *remote_port);

/** Close a connection */
int tnet_disconnect(tnet_stack_t *stack, int conn_id);

/** Get connection state */
trit tnet_conn_state(const tnet_stack_t *stack, int conn_id);

/* ==== ARP Cache ========================================================= */

/** Add/update ARP entry */
int tnet_arp_update(tnet_stack_t *stack, const tnet_addr_t *addr, int hw_id);

/** Lookup hardware ID by network address */
int tnet_arp_lookup(tnet_stack_t *stack, const tnet_addr_t *addr);

/* ==== Ping Utility ====================================================== */

/** Send ping (echo request) and check for reply via loopback */
int tnet_ping(tnet_stack_t *stack, const tnet_addr_t *target);

/* ==== Statistics ========================================================= */

/** Get stack statistics */
void tnet_stats(const tnet_stack_t *stack,
                int *tx, int *rx, int *errors, int *connections);

#ifdef __cplusplus
}
#endif

#endif /* TRIT_LINUX_TRIT_NET_H */
