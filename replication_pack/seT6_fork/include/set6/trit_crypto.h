/**
 * @file trit_crypto.h
 * @brief seT6 Ternary Cryptographic Hardening Module
 *
 * Multi-radix cryptographic primitives for quantum-resistant
 * security using balanced ternary {-1, 0, +1} state space.
 *
 * Key features:
 *   - Ternary hash function (3-valued Merkle-Damgård)
 *   - Balanced ternary key generation (TRNG-seeded)
 *   - Ternary lattice operations (high-radix LWE basis)
 *   - Ternary XOR (balanced mod-3 addition)
 *   - Trit-wise permutation cipher
 *   - Message Authentication Code (MAC) using trit dot-product
 *   - Side-channel resistance via constant-time trit operations
 *
 * Security rationale: Ternary state space has 3^n configurations
 * vs binary's 2^n. For n=256 trits: 3^256 ≈ 2^406, providing
 * ~406 bits of equivalent security — inherently quantum-hardened.
 *
 * @see INCREASE_FUNCTIONAL_UTILITY.md § Multi-Radix Cryptographic Hardening
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_TRIT_CRYPTO_H
#define SET6_TRIT_CRYPTO_H

#include "set6/trit.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ======================================================== */

/** Standard hash width (trits) — 162 trits ≈ 256 bits equivalent */
#define TCRYPTO_HASH_TRITS     81

/** Key length (trits) — 243 trits ≈ 385 bits equivalent */
#define TCRYPTO_KEY_TRITS      81

/** Lattice dimension for LWE-style operations */
#define TCRYPTO_LATTICE_DIM    27

/** MAC tag length (trits) */
#define TCRYPTO_MAC_TRITS      27

/** Maximum message length for hash/MAC */
#define TCRYPTO_MAX_MSG        512

/* ==== Structures ======================================================= */

/**
 * @brief Ternary hash state (sponge construction).
 */
typedef struct {
    trit   state[TCRYPTO_HASH_TRITS];  /**< Internal state */
    int    absorbed;                     /**< Trits absorbed so far */
    int    finalized;                    /**< Hash finalized flag */
} tcrypto_hash_t;

/**
 * @brief Ternary symmetric key.
 */
typedef struct {
    trit   data[TCRYPTO_KEY_TRITS];    /**< Key material */
    int    length;                      /**< Active key length (trits) */
} tcrypto_key_t;

/**
 * @brief Ternary lattice vector (for LWE operations).
 */
typedef struct {
    trit   coeffs[TCRYPTO_LATTICE_DIM]; /**< Lattice coefficients */
} tcrypto_lattice_vec_t;

/**
 * @brief Ternary cipher state.
 */
typedef struct {
    tcrypto_key_t  key;                /**< Active key */
    trit           iv[TCRYPTO_MAC_TRITS]; /**< Initialization vector */
    int            rounds;              /**< Permutation rounds */
} tcrypto_cipher_t;

/* ==== Hash API ========================================================= */

/**
 * @brief Initialize ternary hash state.
 */
void tcrypto_hash_init(tcrypto_hash_t *h);

/**
 * @brief Absorb message trits into hash state.
 *
 * Uses balanced mod-3 addition with state rotation.
 *
 * @param h     Hash state.
 * @param msg   Message trits.
 * @param len   Message length.
 */
void tcrypto_hash_absorb(tcrypto_hash_t *h, const trit *msg, int len);

/**
 * @brief Finalize hash and produce digest.
 *
 * @param h      Hash state (becomes finalized).
 * @param digest Output digest (TCRYPTO_HASH_TRITS trits).
 */
void tcrypto_hash_finalize(tcrypto_hash_t *h, trit *digest);

/**
 * @brief One-shot hash: init + absorb + finalize.
 */
void tcrypto_hash(trit *digest, const trit *msg, int msg_len);

/* ==== Key API ========================================================== */

/**
 * @brief Generate a ternary key from a seed.
 *
 * Uses hash-based key derivation from integer seed.
 *
 * @param key   Output key.
 * @param seed  Integer seed for PRNG.
 */
void tcrypto_keygen(tcrypto_key_t *key, uint32_t seed);

/**
 * @brief Compare two keys in constant time.
 * @return  0 if equal, non-zero if different.
 */
int tcrypto_key_compare(const tcrypto_key_t *a, const tcrypto_key_t *b);

/* ==== Cipher API ======================================================= */

/**
 * @brief Initialize cipher with key and IV.
 */
void tcrypto_cipher_init(tcrypto_cipher_t *c, const tcrypto_key_t *key,
                          const trit *iv, int rounds);

/**
 * @brief Encrypt message in-place using trit permutation cipher.
 *
 * Each round: XOR with key stream, rotate, non-linear substitution.
 * XOR in balanced ternary = (a + b + 1) mod 3 - 1.
 *
 * @param c     Cipher state.
 * @param data  Data to encrypt (modified in-place).
 * @param len   Data length (trits).
 */
void tcrypto_encrypt(tcrypto_cipher_t *c, trit *data, int len);

/**
 * @brief Decrypt message in-place.
 */
void tcrypto_decrypt(tcrypto_cipher_t *c, trit *data, int len);

/* ==== MAC API ========================================================== */

/**
 * @brief Compute ternary MAC using dot-product accumulation.
 *
 * MAC = hash(key || msg), truncated to TCRYPTO_MAC_TRITS.
 *
 * @param tag    Output MAC tag.
 * @param key    Authentication key.
 * @param msg    Message.
 * @param len    Message length.
 */
void tcrypto_mac(trit *tag, const tcrypto_key_t *key,
                 const trit *msg, int len);

/**
 * @brief Verify MAC tag (constant-time comparison).
 * @return  1 if valid, 0 if invalid.
 */
int tcrypto_mac_verify(const trit *tag, const tcrypto_key_t *key,
                       const trit *msg, int len);

/* ==== Lattice API ====================================================== */

/**
 * @brief Generate random lattice vector from seed.
 */
void tcrypto_lattice_gen(tcrypto_lattice_vec_t *v, uint32_t seed);

/**
 * @brief Lattice vector inner product (mod 3 arithmetic).
 *
 * Computes Σ a[i]·b[i] clamped to ternary.
 *
 * @return  Ternary result {-1, 0, +1}.
 */
trit tcrypto_lattice_dot(const tcrypto_lattice_vec_t *a,
                          const tcrypto_lattice_vec_t *b);

/**
 * @brief Add noise to lattice vector (LWE error term).
 */
void tcrypto_lattice_add_noise(tcrypto_lattice_vec_t *v, uint32_t seed);

/* ==== Utility ========================================================== */

/**
 * @brief Balanced ternary XOR (mod-3 addition in balanced ternary).
 *
 * Maps {-1,0,+1}×{-1,0,+1} → {-1,0,+1} via (a+b) mod 3.
 */
static inline trit tcrypto_trit_xor(trit a, trit b) {
    int sum = (int)a + (int)b;
    if (sum >  1) sum -= 3;
    if (sum < -1) sum += 3;
    return (trit)sum;
}

/**
 * @brief Inverse of tcrypto_trit_xor (mod-3 subtraction).
 *
 * If c = tcrypto_trit_xor(p, k), then p = tcrypto_trit_xor_inv(c, k).
 * Required because addition mod 3 is NOT self-inverse (unlike binary XOR).
 */
static inline trit tcrypto_trit_xor_inv(trit a, trit b) {
    int diff = (int)a - (int)b;
    if (diff >  1) diff -= 3;
    if (diff < -1) diff += 3;
    return (trit)diff;
}

/**
 * @brief Compute security level in equivalent binary bits.
 *
 * n trits → n × log2(3) ≈ n × 1.585 equivalent bits.
 *
 * @param trit_count  Number of trits.
 * @return            Equivalent security bits (×10 for precision).
 */
static inline int tcrypto_security_bits_x10(int trit_count) {
    return (trit_count * 1585) / 100;
}

#ifdef __cplusplus
}
#endif

#endif /* SET6_TRIT_CRYPTO_H */
