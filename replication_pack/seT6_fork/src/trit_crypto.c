/**
 * @file trit_crypto.c
 * @brief seT6 Ternary Cryptographic Hardening — Implementation
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set6/trit_crypto.h"
#include <string.h>

/* ---- Internal helpers ------------------------------------------------- */

/** xorshift32 PRNG */
static uint32_t crypto_xorshift(uint32_t *seed) {
    uint32_t x = *seed;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    *seed = x;
    return x;
}

/** Generate trit from PRNG: maps to {-1, 0, +1} */
static trit trit_from_rng(uint32_t *seed) {
    uint32_t r = crypto_xorshift(seed) % 3;
    return (trit)((int)r - 1);
}

/** Non-linear substitution (ternary S-box) */
static trit sbox(trit a) {
    /* S: -1→1, 0→-1, 1→0 (cyclic rotation) */
    switch (a) {
        case TRIT_FALSE:   return TRIT_TRUE;
        case TRIT_UNKNOWN: return TRIT_FALSE;
        case TRIT_TRUE:    return TRIT_UNKNOWN;
        default:           return TRIT_UNKNOWN;
    }
}

/** Inverse S-box */
static trit sbox_inv(trit a) {
    /* S^{-1}: 1→-1, -1→0, 0→1 */
    switch (a) {
        case TRIT_TRUE:    return TRIT_FALSE;
        case TRIT_FALSE:   return TRIT_UNKNOWN;
        case TRIT_UNKNOWN: return TRIT_TRUE;
        default:           return TRIT_UNKNOWN;
    }
}

/* ---- Hash API --------------------------------------------------------- */

void tcrypto_hash_init(tcrypto_hash_t *h) {
    memset(h, 0, sizeof(*h));
    /* Initialize state with non-zero pattern */
    for (int i = 0; i < TCRYPTO_HASH_TRITS; i++)
        h->state[i] = (trit)((i % 3) - 1);
}

void tcrypto_hash_absorb(tcrypto_hash_t *h, const trit *msg, int len) {
    if (h->finalized) return;

    for (int i = 0; i < len; i++) {
        int idx = h->absorbed % TCRYPTO_HASH_TRITS;

        /* XOR (balanced mod-3 addition) with state */
        h->state[idx] = tcrypto_trit_xor(h->state[idx], msg[i]);

        /* Diffusion: rotate state and apply S-box to neighbor */
        int next = (idx + 1) % TCRYPTO_HASH_TRITS;
        h->state[next] = sbox(tcrypto_trit_xor(h->state[next], h->state[idx]));

        h->absorbed++;

        /* Permutation round every HASH_TRITS absorbed */
        if (h->absorbed % TCRYPTO_HASH_TRITS == 0) {
            /* Full-state permutation */
            for (int j = 0; j < TCRYPTO_HASH_TRITS; j++) {
                int target = (j * 7 + 3) % TCRYPTO_HASH_TRITS;
                h->state[target] = sbox(tcrypto_trit_xor(h->state[target],
                                        h->state[j]));
            }
        }
    }
}

void tcrypto_hash_finalize(tcrypto_hash_t *h, trit *digest) {
    if (h->finalized) {
        memcpy(digest, h->state, TCRYPTO_HASH_TRITS * sizeof(trit));
        return;
    }

    /* Final permutation rounds (3 rounds for security) */
    for (int round = 0; round < 3; round++) {
        for (int i = 0; i < TCRYPTO_HASH_TRITS; i++) {
            int j = (i * 11 + round * 7 + 1) % TCRYPTO_HASH_TRITS;
            h->state[i] = sbox(tcrypto_trit_xor(h->state[i], h->state[j]));
        }
    }

    h->finalized = 1;
    memcpy(digest, h->state, TCRYPTO_HASH_TRITS * sizeof(trit));
}

void tcrypto_hash(trit *digest, const trit *msg, int msg_len) {
    tcrypto_hash_t h;
    tcrypto_hash_init(&h);
    tcrypto_hash_absorb(&h, msg, msg_len);
    tcrypto_hash_finalize(&h, digest);
}

/* ---- Key API ---------------------------------------------------------- */

void tcrypto_keygen(tcrypto_key_t *key, uint32_t seed) {
    uint32_t rng = seed;

    key->length = TCRYPTO_KEY_TRITS;
    for (int i = 0; i < TCRYPTO_KEY_TRITS; i++)
        key->data[i] = trit_from_rng(&rng);

    /* Hash the raw key for uniformity */
    trit digest[TCRYPTO_HASH_TRITS];
    tcrypto_hash(digest, key->data, TCRYPTO_KEY_TRITS);
    memcpy(key->data, digest, TCRYPTO_KEY_TRITS * sizeof(trit));
}

int tcrypto_key_compare(const tcrypto_key_t *a, const tcrypto_key_t *b) {
    /* Constant-time comparison to prevent timing attacks */
    int diff = 0;
    int len = (a->length < b->length) ? a->length : b->length;
    diff |= (a->length ^ b->length);
    for (int i = 0; i < len; i++)
        diff |= (a->data[i] ^ b->data[i]);
    return diff;
}

/* ---- Cipher API ------------------------------------------------------- */

void tcrypto_cipher_init(tcrypto_cipher_t *c, const tcrypto_key_t *key,
                          const trit *iv, int rounds) {
    c->key    = *key;
    c->rounds = (rounds > 0) ? rounds : 12;
    if (iv)
        memcpy(c->iv, iv, TCRYPTO_MAC_TRITS * sizeof(trit));
    else
        memset(c->iv, 0, TCRYPTO_MAC_TRITS * sizeof(trit));
}

void tcrypto_encrypt(tcrypto_cipher_t *c, trit *data, int len) {
    for (int round = 0; round < c->rounds; round++) {
        for (int i = 0; i < len; i++) {
            /* XOR with key stream */
            int key_idx = (i + round) % c->key.length;
            data[i] = tcrypto_trit_xor(data[i], c->key.data[key_idx]);

            /* XOR with IV */
            int iv_idx = i % TCRYPTO_MAC_TRITS;
            data[i] = tcrypto_trit_xor(data[i], c->iv[iv_idx]);

            /* Non-linear substitution */
            data[i] = sbox(data[i]);
        }

        /* Rotate data by round offset */
        if (len > 1) {
            trit temp = data[len - 1];
            for (int i = len - 1; i > 0; i--)
                data[i] = data[i - 1];
            data[0] = temp;
        }
    }
}

void tcrypto_decrypt(tcrypto_cipher_t *c, trit *data, int len) {
    for (int round = c->rounds - 1; round >= 0; round--) {
        /* Inverse rotate */
        if (len > 1) {
            trit temp = data[0];
            for (int i = 0; i < len - 1; i++)
                data[i] = data[i + 1];
            data[len - 1] = temp;
        }

        for (int i = len - 1; i >= 0; i--) {
            /* Inverse substitution */
            data[i] = sbox_inv(data[i]);

            /* Inverse XOR with IV (subtraction undoes addition) */
            int iv_idx = i % TCRYPTO_MAC_TRITS;
            data[i] = tcrypto_trit_xor_inv(data[i], c->iv[iv_idx]);

            /* Inverse XOR with key stream (subtraction undoes addition) */
            int key_idx = (i + round) % c->key.length;
            data[i] = tcrypto_trit_xor_inv(data[i], c->key.data[key_idx]);
        }
    }
}

/* ---- MAC API ---------------------------------------------------------- */

void tcrypto_mac(trit *tag, const tcrypto_key_t *key,
                 const trit *msg, int len) {
    tcrypto_hash_t h;
    tcrypto_hash_init(&h);

    /* Absorb key first */
    tcrypto_hash_absorb(&h, key->data, key->length);
    /* Then message */
    tcrypto_hash_absorb(&h, msg, len);

    trit digest[TCRYPTO_HASH_TRITS];
    tcrypto_hash_finalize(&h, digest);

    /* Truncate to MAC length */
    memcpy(tag, digest, TCRYPTO_MAC_TRITS * sizeof(trit));
}

int tcrypto_mac_verify(const trit *tag, const tcrypto_key_t *key,
                       const trit *msg, int len) {
    trit computed[TCRYPTO_MAC_TRITS];
    tcrypto_mac(computed, key, msg, len);

    /* Constant-time comparison */
    int diff = 0;
    for (int i = 0; i < TCRYPTO_MAC_TRITS; i++)
        diff |= (computed[i] ^ tag[i]);

    return (diff == 0) ? 1 : 0;
}

/* ---- Lattice API ------------------------------------------------------ */

void tcrypto_lattice_gen(tcrypto_lattice_vec_t *v, uint32_t seed) {
    uint32_t rng = seed;
    for (int i = 0; i < TCRYPTO_LATTICE_DIM; i++)
        v->coeffs[i] = trit_from_rng(&rng);
}

trit tcrypto_lattice_dot(const tcrypto_lattice_vec_t *a,
                          const tcrypto_lattice_vec_t *b) {
    int acc = 0;
    for (int i = 0; i < TCRYPTO_LATTICE_DIM; i++)
        acc += (int)a->coeffs[i] * (int)b->coeffs[i];

    /* Clamp to ternary */
    if (acc > 0) return TRIT_TRUE;
    if (acc < 0) return TRIT_FALSE;
    return TRIT_UNKNOWN;
}

void tcrypto_lattice_add_noise(tcrypto_lattice_vec_t *v, uint32_t seed) {
    uint32_t rng = seed;
    for (int i = 0; i < TCRYPTO_LATTICE_DIM; i++) {
        /* Flip ~10% of elements */
        if ((crypto_xorshift(&rng) % 10) == 0) {
            v->coeffs[i] = trit_from_rng(&rng);
        }
    }
}
