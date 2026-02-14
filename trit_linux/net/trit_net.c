/**
 * @file trit_net.c
 * @brief Trit Linux — Ternary-Optimized Networking Stack Implementation
 *
 * Implements the T-Net protocol with Kleene firewall, connection tracking,
 * ARP cache, and XOR-based ternary checksums. All operations run in
 * user-space, interfacing through T-IPC for inter-process messaging.
 *
 * Enhancement 2: "Ternary-Optimized Networking Stack"
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include "trit_net.h"

/* ==================================================================== */
/*  Address/Port Utilities                                              */
/* ==================================================================== */

void tnet_addr_from_int(tnet_addr_t *addr, int value) {
    if (!addr) return;
    memset(addr, 0, sizeof(*addr));

    /*
     * Convert integer to balanced ternary digits.
     * Algorithm: repeated division with offset (same as RADIX_CONV).
     * Handles negative values through sign adjustment.
     */
    int n = (value < 0) ? -value : value;
    int sign = (value < 0) ? -1 : 1;

    for (int i = 0; i < TNET_ADDR_TRITS && n != 0; i++) {
        int r = n % 3;
        if (r == 0)      { addr->digits[i] = 0;            n = n / 3; }
        else if (r == 1)  { addr->digits[i] = sign * 1;    n = (n - 1) / 3; }
        else              { addr->digits[i] = sign * (-1);  n = (n + 1) / 3; }
    }
}

int tnet_addr_to_int(const tnet_addr_t *addr) {
    if (!addr) return 0;
    int result = 0;
    int power = 1; /* 3^i */

    for (int i = 0; i < TNET_ADDR_TRITS; i++) {
        result += addr->digits[i] * power;
        power *= 3;
    }
    return result;
}

int tnet_addr_equal(const tnet_addr_t *a, const tnet_addr_t *b) {
    if (!a || !b) return 0;
    for (int i = 0; i < TNET_ADDR_TRITS; i++) {
        if (a->digits[i] != b->digits[i]) return 0;
    }
    return 1;
}

void tnet_port_from_int(tnet_port_t *port, int value) {
    if (!port) return;
    memset(port, 0, sizeof(*port));

    int n = (value < 0) ? -value : value;
    int sign = (value < 0) ? -1 : 1;

    for (int i = 0; i < TNET_PORT_TRITS && n != 0; i++) {
        int r = n % 3;
        if (r == 0)      { port->digits[i] = 0;            n = n / 3; }
        else if (r == 1)  { port->digits[i] = sign * 1;    n = (n - 1) / 3; }
        else              { port->digits[i] = sign * (-1);  n = (n + 1) / 3; }
    }
}

int tnet_port_to_int(const tnet_port_t *port) {
    if (!port) return 0;
    int result = 0, power = 1;
    for (int i = 0; i < TNET_PORT_TRITS; i++) {
        result += port->digits[i] * power;
        power *= 3;
    }
    return result;
}

/* ==================================================================== */
/*  Initialization                                                      */
/* ==================================================================== */

int tnet_init(tnet_stack_t *stack, const tnet_addr_t *addr) {
    if (!stack || !addr) return TNET_ERR_INIT;

    memset(stack, 0, sizeof(*stack));

    /* Set local address */
    stack->local_addr = *addr;

    /* Initialize multi-radix engine for checksums and encryption */
    multiradix_init(&stack->mr);

    /* Initialize packet queues (ring buffers) */
    stack->tx_head = stack->tx_tail = stack->tx_count = 0;
    stack->rx_head = stack->rx_tail = stack->rx_count = 0;

    /* Mark all connections as closed (TRIT_FALSE) */
    for (int i = 0; i < TNET_MAX_CONNECTIONS; i++) {
        stack->connections[i].state = TRIT_FALSE;
    }

    /* Clear ARP cache */
    for (int i = 0; i < TNET_ARP_CACHE_SIZE; i++) {
        stack->arp_cache[i].valid = 0;
    }

    /* Clear firewall rules */
    stack->fw_rule_count = 0;

    stack->seq_next = 1;
    stack->initialized = 1;

    return TNET_OK;
}

/* ==================================================================== */
/*  Checksum — 6-trit XOR-based ternary checksum                       */
/* ==================================================================== */

void tnet_checksum_compute(trit *checksum, const trit *data, int len) {
    if (!checksum || !data) return;

    /*
     * Compute a 6-trit checksum by accumulating trit values modulo 3.
     * Uses cyclic XOR-like accumulation across 6 trit positions.
     * This is the ternary analog of CRC, exploiting balanced representation.
     */
    int accum[TNET_CHECKSUM_TRITS] = {0};

    for (int i = 0; i < len; i++) {
        accum[i % TNET_CHECKSUM_TRITS] += data[i];
    }

    /* Reduce each accumulator to balanced ternary range {-1, 0, +1} */
    for (int i = 0; i < TNET_CHECKSUM_TRITS; i++) {
        int v = ((accum[i] % 3) + 3) % 3;
        if (v == 0)      checksum[i] = 0;
        else if (v == 1) checksum[i] = 1;
        else             checksum[i] = -1;
    }
}

int tnet_checksum_verify(const tnet_packet_t *pkt) {
    if (!pkt) return 0;

    trit expected[TNET_CHECKSUM_TRITS];
    tnet_checksum_compute(expected, pkt->payload, pkt->header.payload_len);

    for (int i = 0; i < TNET_CHECKSUM_TRITS; i++) {
        if (expected[i] != pkt->header.checksum[i]) return 0;
    }
    return 1;
}

/* ==================================================================== */
/*  Packet Construction                                                 */
/* ==================================================================== */

int tnet_build_packet(tnet_packet_t *pkt,
                      const tnet_addr_t *src, const tnet_addr_t *dst,
                      const tnet_port_t *sport, const tnet_port_t *dport,
                      int protocol, const trit *payload, int len) {
    if (!pkt || !src || !dst) return TNET_ERR_INIT;
    if (len > TNET_MAX_PAYLOAD) len = TNET_MAX_PAYLOAD;

    memset(pkt, 0, sizeof(*pkt));

    /* Fill header */
    pkt->header.src_addr = *src;
    pkt->header.dst_addr = *dst;
    if (sport) pkt->header.src_port = *sport;
    if (dport) pkt->header.dst_port = *dport;
    pkt->header.protocol = protocol;
    pkt->header.payload_len = len;
    pkt->header.ttl = 16; /* Default TTL */

    /* Copy payload */
    if (payload && len > 0) {
        memcpy(pkt->payload, payload, sizeof(trit) * len);
    }

    /* Compute checksum over payload */
    tnet_checksum_compute(pkt->header.checksum, pkt->payload, len);

    pkt->valid = 1;
    return TNET_OK;
}

/* ==================================================================== */
/*  Firewall — Kleene-state packet filter                               */
/* ==================================================================== */

int tnet_fw_add_rule(tnet_stack_t *stack, const tnet_addr_t *src_mask,
                     const tnet_port_t *port_mask, int protocol, trit action) {
    if (!stack || stack->fw_rule_count >= TNET_MAX_FIREWALL) return TNET_ERR_FULL;

    tnet_firewall_rule_t *rule = &stack->firewall[stack->fw_rule_count];
    memset(rule, 0, sizeof(*rule));

    if (src_mask) rule->src_mask = *src_mask;
    if (port_mask) rule->port_mask = *port_mask;
    rule->protocol = protocol;
    rule->action = action;
    rule->match_count = 0;
    rule->active = 1;

    stack->fw_rule_count++;
    return TNET_OK;
}

trit tnet_fw_evaluate(tnet_stack_t *stack, const tnet_packet_t *pkt) {
    if (!stack || !pkt) return TRIT_FALSE;

    /*
     * Evaluate packet against all active firewall rules in order.
     * First matching rule determines the action:
     *   +1 (True)    = ALLOW — pass immediately
     *    0 (Unknown) = INSPECT — log and pass (stateful inspection)
     *   -1 (False)   = DENY — drop silently
     *
     * If no rules match, default action is ALLOW (permissive).
     */
    for (int i = 0; i < stack->fw_rule_count; i++) {
        tnet_firewall_rule_t *rule = &stack->firewall[i];
        if (!rule->active) continue;

        /* Check protocol match (-1 = match any) */
        if (rule->protocol >= 0 && rule->protocol != pkt->header.protocol) {
            continue;
        }

        /*
         * Check source address mask: a zero trit in the mask means
         * "wildcard" (match any). Non-zero means must match.
         */
        int addr_match = 1;
        for (int j = 0; j < TNET_ADDR_TRITS; j++) {
            if (rule->src_mask.digits[j] != 0 &&
                rule->src_mask.digits[j] != pkt->header.src_addr.digits[j]) {
                addr_match = 0;
                break;
            }
        }
        if (!addr_match) continue;

        /* Rule matched — apply action */
        rule->match_count++;

        switch (rule->action) {
            case TRIT_TRUE:
                stack->fw_allowed++;
                return TRIT_TRUE;
            case TRIT_UNKNOWN:
                stack->fw_inspected++;
                return TRIT_UNKNOWN;
            case TRIT_FALSE:
                stack->fw_denied++;
                return TRIT_FALSE;
            default:
                break;
        }
    }

    /* Default policy: ALLOW if no rules match */
    stack->fw_allowed++;
    return TRIT_TRUE;
}

void tnet_fw_stats(const tnet_stack_t *stack,
                   int *denied, int *inspected, int *allowed) {
    if (!stack) return;
    if (denied)    *denied    = stack->fw_denied;
    if (inspected) *inspected = stack->fw_inspected;
    if (allowed)   *allowed   = stack->fw_allowed;
}

/* ==================================================================== */
/*  Send / Receive — TX/RX ring buffer operations                       */
/* ==================================================================== */

int tnet_send(tnet_stack_t *stack, const tnet_addr_t *dst,
              const tnet_port_t *dport, int protocol,
              const trit *payload, int len) {
    if (!stack || !stack->initialized || !dst) return TNET_ERR_INIT;
    if (stack->tx_count >= TNET_TX_QUEUE_SIZE) return TNET_ERR_FULL;

    /* Build packet with our local address as source */
    tnet_port_t default_port;
    memset(&default_port, 0, sizeof(default_port));

    tnet_packet_t *pkt = &stack->tx_queue[stack->tx_tail];
    int rc = tnet_build_packet(pkt, &stack->local_addr, dst,
                               &default_port, dport ? dport : &default_port,
                               protocol, payload, len);
    if (rc != TNET_OK) return rc;

    /* Assign sequence number */
    pkt->header.seq_num = stack->seq_next++;

    /* Advance TX ring buffer */
    stack->tx_tail = (stack->tx_tail + 1) % TNET_TX_QUEUE_SIZE;
    stack->tx_count++;
    stack->total_tx++;

    return TNET_OK;
}

int tnet_recv(tnet_stack_t *stack, tnet_packet_t *pkt) {
    if (!stack || !pkt || !stack->initialized) return TNET_ERR_INIT;
    if (stack->rx_count == 0) return TNET_ERR_NOCONN;

    /* Dequeue from RX ring buffer */
    *pkt = stack->rx_queue[stack->rx_head];
    stack->rx_head = (stack->rx_head + 1) % TNET_RX_QUEUE_SIZE;
    stack->rx_count--;

    return TNET_OK;
}

int tnet_loopback(tnet_stack_t *stack) {
    if (!stack || !stack->initialized) return TNET_ERR_INIT;

    int looped = 0;

    /*
     * Move all TX packets addressed to our local address into the RX queue.
     * Verifies checksums before accepting. Applies firewall rules.
     */
    while (stack->tx_count > 0) {
        tnet_packet_t pkt = stack->tx_queue[stack->tx_head];
        stack->tx_head = (stack->tx_head + 1) % TNET_TX_QUEUE_SIZE;
        stack->tx_count--;

        /* Check if destination matches our address */
        if (!tnet_addr_equal(&pkt.header.dst_addr, &stack->local_addr)) {
            continue; /* Not for us */
        }

        /* Verify checksum */
        if (!tnet_checksum_verify(&pkt)) {
            stack->checksum_errors++;
            continue;
        }

        /* Apply firewall evaluation */
        trit fw_result = tnet_fw_evaluate(stack, &pkt);
        if (fw_result == TRIT_FALSE) {
            continue; /* Denied */
        }

        /* Accept packet into RX queue */
        if (stack->rx_count < TNET_RX_QUEUE_SIZE) {
            stack->rx_queue[stack->rx_tail] = pkt;
            stack->rx_tail = (stack->rx_tail + 1) % TNET_RX_QUEUE_SIZE;
            stack->rx_count++;
            stack->total_rx++;
            looped++;
        }
    }

    return looped;
}

/* ==================================================================== */
/*  Connection Management                                               */
/* ==================================================================== */

int tnet_connect(tnet_stack_t *stack, const tnet_addr_t *remote,
                 const tnet_port_t *local_port, const tnet_port_t *remote_port) {
    if (!stack || !remote || !stack->initialized) return TNET_ERR_INIT;

    /* Find a free connection slot */
    for (int i = 0; i < TNET_MAX_CONNECTIONS; i++) {
        if (stack->connections[i].state == TRIT_FALSE) {
            tnet_connection_t *conn = &stack->connections[i];
            conn->remote_addr = *remote;
            if (local_port) conn->local_port = *local_port;
            if (remote_port) conn->remote_port = *remote_port;
            conn->state = TRIT_UNKNOWN; /* Half-open */
            conn->tx_seq = 0;
            conn->rx_seq = 0;
            conn->tx_count = 0;
            conn->rx_count = 0;

            stack->conn_count++;

            /*
             * Simulate handshake: send DATA, loopback to self → ESTABLISHED.
             * In a real implementation, this would be asynchronous.
             */
            conn->state = TRIT_TRUE; /* Established */

            return i; /* Return connection ID */
        }
    }

    return TNET_ERR_FULL;
}

int tnet_disconnect(tnet_stack_t *stack, int conn_id) {
    if (!stack || conn_id < 0 || conn_id >= TNET_MAX_CONNECTIONS)
        return TNET_ERR_NOCONN;

    tnet_connection_t *conn = &stack->connections[conn_id];
    if (conn->state == TRIT_FALSE) return TNET_ERR_NOCONN;

    conn->state = TRIT_FALSE; /* Closed */
    stack->conn_count--;

    return TNET_OK;
}

trit tnet_conn_state(const tnet_stack_t *stack, int conn_id) {
    if (!stack || conn_id < 0 || conn_id >= TNET_MAX_CONNECTIONS)
        return TRIT_FALSE;
    return stack->connections[conn_id].state;
}

/* ==================================================================== */
/*  ARP Cache                                                           */
/* ==================================================================== */

int tnet_arp_update(tnet_stack_t *stack, const tnet_addr_t *addr, int hw_id) {
    if (!stack || !addr) return TNET_ERR_INIT;

    /* Check if entry already exists — update if so */
    for (int i = 0; i < TNET_ARP_CACHE_SIZE; i++) {
        if (stack->arp_cache[i].valid &&
            tnet_addr_equal(&stack->arp_cache[i].net_addr, addr)) {
            stack->arp_cache[i].hw_id = hw_id;
            stack->arp_cache[i].age = 0;
            return TNET_OK;
        }
    }

    /* Find a free slot */
    for (int i = 0; i < TNET_ARP_CACHE_SIZE; i++) {
        if (!stack->arp_cache[i].valid) {
            stack->arp_cache[i].net_addr = *addr;
            stack->arp_cache[i].hw_id = hw_id;
            stack->arp_cache[i].valid = 1;
            stack->arp_cache[i].age = 0;
            stack->arp_count++;
            return TNET_OK;
        }
    }

    return TNET_ERR_FULL; /* Cache full */
}

int tnet_arp_lookup(tnet_stack_t *stack, const tnet_addr_t *addr) {
    if (!stack || !addr) return -1;

    for (int i = 0; i < TNET_ARP_CACHE_SIZE; i++) {
        if (stack->arp_cache[i].valid &&
            tnet_addr_equal(&stack->arp_cache[i].net_addr, addr)) {
            stack->arp_cache[i].age = 0; /* Refresh on use */
            return stack->arp_cache[i].hw_id;
        }
    }

    return -1; /* Not found */
}

/* ==================================================================== */
/*  Ping Utility                                                        */
/* ==================================================================== */

int tnet_ping(tnet_stack_t *stack, const tnet_addr_t *target) {
    if (!stack || !target || !stack->initialized) return TNET_ERR_INIT;

    /*
     * Send a PING packet with 4-trit payload {1, 0, -1, 1}.
     * If target is our own address, loopback will deliver it
     * and we return success (1). Otherwise return 0 (no reply).
     */
    trit ping_payload[4] = {1, 0, -1, 1};
    int rc = tnet_send(stack, target, NULL, TNET_PROTO_PING, ping_payload, 4);
    if (rc != TNET_OK) return rc;

    /* Try loopback */
    int looped = tnet_loopback(stack);

    if (looped > 0) {
        /* Check if we got a ping back */
        tnet_packet_t reply;
        if (tnet_recv(stack, &reply) == TNET_OK) {
            if (reply.header.protocol == TNET_PROTO_PING) {
                return 1; /* Ping success */
            }
        }
    }

    return 0; /* No reply (timeout in real system) */
}

/* ==================================================================== */
/*  Statistics                                                          */
/* ==================================================================== */

void tnet_stats(const tnet_stack_t *stack,
                int *tx, int *rx, int *errors, int *connections) {
    if (!stack) return;
    if (tx)          *tx          = stack->total_tx;
    if (rx)          *rx          = stack->total_rx;
    if (errors)      *errors      = stack->checksum_errors;
    if (connections) *connections  = stack->conn_count;
}
