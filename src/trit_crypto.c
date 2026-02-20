/**
 * @file trit_crypto.c
 * @brief seT5 Ternary Cryptographic Hardening — Implementation
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/trit_crypto.h"
#include <string.h>

/* ---- Internal helpers ------------------------------------------------- */

/** xorshift32 PRNG (binary — legacy, used as fallback) */
static uint32_t crypto_xorshift(uint32_t *seed) {
    uint32_t x = *seed;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    *seed = x;
    return x;
}

/* ---- T-027: GF(3) LFSR — native ternary PRNG ------------------------- */

/**
 * @brief GF(3) addition: balanced ternary mod-3 add.
 * Maps {-1,0,+1} × {-1,0,+1} → {-1,0,+1}.
 * Equivalent to (a + b + 3) % 3 − 1 on the shifted representation.
 */
static trit gf3_add(trit a, trit b) {
    int s = (int)a + (int)b;
    if (s > 1)  return (trit)(s - 3);
    if (s < -1) return (trit)(s + 3);
    return (trit)s;
}

/**
 * @brief GF(3) multiplication: balanced ternary mod-3 multiply.
 */
static trit gf3_mul(trit a, trit b) {
    return (trit)((int)a * (int)b);
}

/**
 * @brief GF(3) LFSR step — native ternary pseudorandom sequence.
 *
 * 8-trit register with feedback taps using GF(3) arithmetic.
 * Feedback polynomial: x^8 + x^4 + x^3 + x^2 + 1 over GF(3).
 * Period: up to 3^8 − 1 = 6560.
 *
 * @param state  Array of 8 trits (LFSR register)
 * @return       Output trit (former state[7])
 */
static trit gf3_lfsr_step(trit state[8]) {
    /* Output is the last register element */
    trit out = state[7];

    /* Feedback = state[7] + state[3] + state[2] + state[1] (mod 3) */
    trit fb = gf3_add(gf3_add(state[7], state[3]),
                      gf3_add(state[2], state[1]));

    /* Shift right */
    for (int i = 7; i > 0; i--) {
        state[i] = state[i - 1];
    }
    state[0] = fb;

    return out;
}

/**
 * @brief Initialize GF(3) LFSR from a 32-bit binary seed.
 * Maps each 2-bit pair of the seed to a trit.
 */
static void gf3_lfsr_seed(trit state[8], uint32_t seed) {
    for (int i = 0; i < 8; i++) {
        int bits = (seed >> (i * 2)) & 0x03;
        /* Map: 0→unk(0), 1→true(+1), 2→false(-1), 3→true(+1) */
        static const trit map[4] = {0, 1, -1, 1};
        state[i] = map[bits];
    }
    /* Ensure not all-zero (degenerate) */
    if (state[0] == 0 && state[1] == 0 && state[2] == 0 && state[3] == 0 &&
        state[4] == 0 && state[5] == 0 && state[6] == 0 && state[7] == 0) {
        state[0] = TRIT_TRUE;
    }
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

/* VULN-23 fix: full-entropy trit seed instead of 32-bit integer */
void tcrypto_keygen(tcrypto_key_t *key, const trit *seed, int seed_len) {
    if (!key) return;

    key->length = TCRYPTO_KEY_TRITS;

    /* Derive key from seed using hash-based expansion */
    if (seed && seed_len > 0) {
        trit digest[TCRYPTO_HASH_TRITS];
        tcrypto_hash(digest, seed, seed_len);
        /* Use hash output as key material */
        int copy = (TCRYPTO_HASH_TRITS < TCRYPTO_KEY_TRITS) ? TCRYPTO_HASH_TRITS : TCRYPTO_KEY_TRITS;
        memcpy(key->data, digest, copy * sizeof(trit));
        /* If key is longer than hash, do iterative hashing */
        int filled = copy;
        while (filled < TCRYPTO_KEY_TRITS) {
            tcrypto_hash(digest, key->data, filled);
            int chunk = (TCRYPTO_HASH_TRITS < TCRYPTO_KEY_TRITS - filled) ? TCRYPTO_HASH_TRITS : (TCRYPTO_KEY_TRITS - filled);
            memcpy(&key->data[filled], digest, chunk * sizeof(trit));
            filled += chunk;
        }
    } else {
        /* No seed: zero-init (caller's responsibility to provide entropy) */
        for (int i = 0; i < TCRYPTO_KEY_TRITS; i++)
            key->data[i] = TRIT_UNKNOWN;
    }
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

/* ===================================================================== */
/* T-032: NIST FIPS 203 ML-KEM Parameter Alignment                      */
/* ===================================================================== */

/**
 * @brief ML-KEM-512 ternary parameter set.
 *
 * Maps NIST FIPS 203 ML-KEM-512 parameters to the ternary domain:
 *   - n = 256 (polynomial degree)
 *   - k = 2 (module dimension)
 *   - q = 3 (ternary modulus, vs ML-KEM's q=3329)
 *   - η₁ = 3 (noise distribution bound → maps to trit range)
 *   - d_u = 1 trit (ciphertext compression, vs 10 bits)
 *   - d_v = 1 trit (ciphertext compression, vs 4 bits)
 *
 * Ternary advantage: q=3 eliminates modular reduction complexity.
 * The error distribution is inherently centered at 0 with radius 1.
 */
typedef struct {
    int k;           /**< Module dimension (2, 3, or 4)          */
    int n;           /**< Polynomial degree                      */
    int eta1;        /**< Max coefficient magnitude for keygen   */
    int eta2;        /**< Max coefficient magnitude for encaps   */
    int du;          /**< Ciphertext compression (u)             */
    int dv;          /**< Ciphertext compression (v)             */
    const char *name;
} mlkem_trit_params_t;

/* ML-KEM parameter sets mapped to ternary */
static const mlkem_trit_params_t MLKEM_TRIT_512  = {2, 256, 1, 1, 1, 1, "ML-KEM-512/GF3"};
static const mlkem_trit_params_t MLKEM_TRIT_768  = {3, 256, 1, 1, 1, 1, "ML-KEM-768/GF3"};
static const mlkem_trit_params_t MLKEM_TRIT_1024 = {4, 256, 1, 1, 1, 1, "ML-KEM-1024/GF3"};

/**
 * @brief Generate an ML-KEM-style keypair over GF(3).
 *
 * Public key: (A, t = A·s + e)
 * Secret key: s
 * Where A is k×k of n-trit polynomials, s and e are small.
 */
int tcrypto_mlkem_keygen(tcrypto_lattice_vec_t *pk_t,
                          tcrypto_lattice_vec_t *sk_s,
                          uint32_t seed) {
    if (!pk_t || !sk_s) return -1;

    /* s ← small secret (trit vector) */
    tcrypto_lattice_gen(sk_s, seed);

    /* t = A·s + e (simplified: t = hash(s) + noise) */
    tcrypto_lattice_gen(pk_t, seed ^ 0xDEAD);
    for (int i = 0; i < TCRYPTO_LATTICE_DIM; i++) {
        int prod = (int)pk_t->coeffs[i] * (int)sk_s->coeffs[i];
        /* Add noise e */
        trit e = trit_from_rng(&seed);
        int val = prod + (int)e;
        if (val > 1)  val -= 3;
        if (val < -1) val += 3;
        pk_t->coeffs[i] = (trit)val;
    }

    (void)MLKEM_TRIT_512;
    (void)MLKEM_TRIT_768;
    (void)MLKEM_TRIT_1024;

    return 0;
}
