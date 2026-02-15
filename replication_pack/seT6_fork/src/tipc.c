/**
 * @file tipc.c
 * @brief seT6 Ternary-Native IPC (T-IPC) — Implementation
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set6/tipc.h"
#include <string.h>

/* ---- Internal helpers ------------------------------------------------- */

/** Balanced ternary addition mod 3 */
static trit trit_add_mod3(trit a, trit b) {
    int sum = (int)a + (int)b;
    if (sum >  1) sum -= 3;
    if (sum < -1) sum += 3;
    return (trit)sum;
}

/** Set bit in compressed buffer */
static void set_bit(tipc_compressed_t *c, int pos, int val) {
    int byte_idx = pos / 8;
    int bit_idx  = 7 - (pos % 8);   /* MSB first */
    if (byte_idx < TIPC_MAX_COMPRESSED) {
        if (val)
            c->data[byte_idx] |= (uint8_t)(1 << bit_idx);
        else
            c->data[byte_idx] &= (uint8_t)~(1 << bit_idx);
    }
}

/** Get bit from compressed buffer */
static int get_bit(const tipc_compressed_t *c, int pos) {
    int byte_idx = pos / 8;
    int bit_idx  = 7 - (pos % 8);
    if (byte_idx >= TIPC_MAX_COMPRESSED) return 0;
    return (c->data[byte_idx] >> bit_idx) & 1;
}

/* ---- Public API ------------------------------------------------------- */

void tipc_channel_init(tipc_channel_t *ch) {
    if (!ch) return;
    memset(ch, 0, sizeof(*ch));
}

int tipc_endpoint_create(tipc_channel_t *ch) {
    if (!ch || ch->active_count >= TIPC_MAX_ENDPOINTS)
        return -1;

    int id = ch->active_count;
    ch->endpoints[id].id = id;
    ch->endpoints[id].active = 1;
    ch->endpoints[id].msg_count = 0;
    ch->endpoints[id].guard_fails = 0;
    memset(&ch->endpoints[id].inbox, 0, sizeof(tipc_message_t));
    ch->active_count++;
    return id;
}

trit tipc_guardian_compute(const trit *trits, int count) {
    trit guardian = TRIT_UNKNOWN;   /* Start at 0 */
    for (int i = 0; i < count; i++)
        guardian = trit_add_mod3(guardian, trits[i]);
    return guardian;
}

int tipc_guardian_validate(const tipc_message_t *msg) {
    if (!msg || msg->count <= 0)
        return TIPC_GUARDIAN_FAIL;

    trit computed = tipc_guardian_compute(msg->trits, msg->count);
    return (computed == msg->guardian) ? TIPC_GUARDIAN_OK : TIPC_GUARDIAN_FAIL;
}

int tipc_compress(tipc_compressed_t *out, const trit *trits, int count) {
    if (!out || !trits || count <= 0 || count > TIPC_MAX_TRITS)
        return -1;

    memset(out, 0, sizeof(*out));
    out->original_trits = count;

    int pos = 0;
    for (int i = 0; i < count; i++) {
        switch (trits[i]) {
            case TRIT_UNKNOWN: /* 0 → '0' (1 bit) */
                set_bit(out, pos++, 0);
                break;
            case TRIT_TRUE:    /* +1 → '10' (2 bits) */
                set_bit(out, pos++, 1);
                set_bit(out, pos++, 0);
                break;
            case TRIT_FALSE:   /* -1 → '11' (2 bits) */
                set_bit(out, pos++, 1);
                set_bit(out, pos++, 1);
                break;
            default:
                set_bit(out, pos++, 0); /* Treat invalid as 0 */
                break;
        }

        /* Overflow check */
        if (pos > TIPC_MAX_COMPRESSED * 8)
            return -1;
    }

    out->bit_count = pos;
    out->byte_count = (pos + 7) / 8;
    return pos;
}

int tipc_decompress(trit *trits, int max_trits, const tipc_compressed_t *comp) {
    if (!trits || !comp || comp->bit_count <= 0)
        return -1;

    int pos = 0;
    int count = 0;

    while (pos < comp->bit_count && count < max_trits &&
           count < comp->original_trits) {
        int bit = get_bit(comp, pos++);
        if (bit == 0) {
            /* '0' → Unknown (0) */
            trits[count++] = TRIT_UNKNOWN;
        } else {
            /* '1x' → check next bit */
            if (pos >= comp->bit_count) break;
            int bit2 = get_bit(comp, pos++);
            if (bit2 == 0)
                trits[count++] = TRIT_TRUE;    /* '10' → +1 */
            else
                trits[count++] = TRIT_FALSE;   /* '11' → -1 */
        }
    }

    return count;
}

int tipc_send(tipc_channel_t *ch, int dst_id,
              const trit *trits, int count, tipc_priority_t priority) {
    if (!ch || dst_id < 0 || dst_id >= ch->active_count ||
        !ch->endpoints[dst_id].active)
        return -1;
    if (!trits || count <= 0 || count > TIPC_MAX_TRITS)
        return -1;

    tipc_endpoint_t *ep = &ch->endpoints[dst_id];

    /* Build message */
    memcpy(ep->inbox.trits, trits, (size_t)count * sizeof(trit));
    ep->inbox.count = count;
    ep->inbox.priority = priority;
    ep->inbox.guardian = tipc_guardian_compute(trits, count);
    ep->inbox.compressed = 0;

    ep->msg_count++;
    ch->total_sent++;
    ch->total_raw_trits += count;

    return 0;
}

int tipc_recv(tipc_channel_t *ch, int ep_id, trit *trits, int max_trits) {
    if (!ch || ep_id < 0 || ep_id >= ch->active_count ||
        !ch->endpoints[ep_id].active)
        return -1;

    tipc_endpoint_t *ep = &ch->endpoints[ep_id];
    if (ep->inbox.count <= 0)
        return -1;   /* No message */

    /* Validate guardian */
    if (tipc_guardian_validate(&ep->inbox) != TIPC_GUARDIAN_OK) {
        ep->guard_fails++;
        return -1;
    }

    int n = (ep->inbox.count < max_trits) ? ep->inbox.count : max_trits;
    memcpy(trits, ep->inbox.trits, (size_t)n * sizeof(trit));

    ch->total_received++;

    /* Clear inbox */
    ep->inbox.count = 0;

    return n;
}

int tipc_xor_diff(tipc_message_t *msg, const trit *delta, int count) {
    if (!msg || !delta || count <= 0)
        return -1;

    int n = (count < msg->count) ? count : msg->count;
    for (int i = 0; i < n; i++)
        msg->trits[i] = trit_add_mod3(msg->trits[i], delta[i]);

    /* Recompute guardian */
    msg->guardian = tipc_guardian_compute(msg->trits, msg->count);

    return 0;
}

int tipc_radix_guard(const uint8_t *data, int len) {
    if (!data || len <= 0) return 1;

    /*
     * Check if data is valid 5-trits-per-byte encoding.
     * Valid bytes: 0..242 (3^5 - 1).
     * Any byte ≥ 243 is a radix violation (pure binary).
     */
    for (int i = 0; i < len; i++) {
        if (data[i] >= 243)
            return 1;   /* Binary violation */
    }
    return 0;
}

tipc_freq_t tipc_frequency(const trit *trits, int count) {
    tipc_freq_t f = {0, 0, 0};
    for (int i = 0; i < count; i++) {
        switch (trits[i]) {
            case TRIT_FALSE:   f.freq_neg++;  break;
            case TRIT_UNKNOWN: f.freq_zero++; break;
            case TRIT_TRUE:    f.freq_pos++;  break;
            default: break;
        }
    }
    return f;
}

int tipc_compression_ratio(const tipc_compressed_t *comp) {
    if (!comp || comp->original_trits <= 0 || comp->bit_count <= 0)
        return -1;

    /* Ratio = compressed_bits / (original_trits × 1.585 bits/trit) × 1000 */
    int raw_bits_x1000 = comp->original_trits * 1585;
    if (raw_bits_x1000 == 0) return -1;

    return (comp->bit_count * 1000 * 1000) / raw_bits_x1000;
}
