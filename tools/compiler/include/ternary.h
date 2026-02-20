#ifndef TERNARY_H
#define TERNARY_H

typedef signed char trit;  // -1 (N), 0 (Z), 1 (P)

#define TRIT_N (-1)
#define TRIT_Z 0
#define TRIT_P 1

// Ternary addition (with carry)
static inline trit trit_add(trit a, trit b, trit *carry) {
    int sum = (int)a + (int)b + (int)*carry;
    if (sum > 1) {
        *carry = TRIT_P;
        return (trit)(sum - 3);
    } else if (sum < -1) {
        *carry = TRIT_N;
        return (trit)(sum + 3);
    } else {
        *carry = TRIT_Z;
        return (trit)sum;
    }
}

// Similar for mul, min, max (from ternary logic gates)
static inline trit trit_mul(trit a, trit b) {
    return (trit)((int)a * (int)b);
}

static inline trit trit_min(trit a, trit b) {
    return (a < b) ? a : b;
}

static inline trit trit_max(trit a, trit b) {
    return (a > b) ? a : b;
}

/* ---- Ternary logic gates (Brusentsov/Jones) ---- */

/* Consensus (ternary AND): outputs the value only if both inputs agree.
 * Truth table: consensus(a,b) = min(a,b)
 * If a and b "agree" (same sign), output that; if they disagree, output 0.
 * This is equivalent to trit_min for balanced ternary. */
static inline trit trit_consensus(trit a, trit b) {
    return trit_min(a, b);
}

/* Accept-any (ternary OR): outputs max of the two inputs.
 * If either input is positive, output is positive. */
static inline trit trit_accept_any(trit a, trit b) {
    return trit_max(a, b);
}

/* Ternary NOT (negation): flip all trits. -1 <-> 1, 0 stays 0.
 * In balanced ternary, negation is simply flipping the sign. */
static inline trit trit_not(trit a) {
    return (trit)(-(int)a);
}

/* Ternary subtraction (with borrow) */
static inline trit trit_sub(trit a, trit b, trit *borrow) {
    /* a - b = a + (-b) */
    trit neg_b = trit_not(b);
    return trit_add(a, neg_b, borrow);
}

/* ---- Multi-trit word operations (TASK-002) ---- */

#define WORD_SIZE 9
typedef trit trit_word[WORD_SIZE];

/* ---- Tryte: 6-trit unit (Setun-70 syllable) ---- */
/*
 * Setun-70 used 6-trit "syllables" (trytes) as the basic unit.
 * Each tryte holds ~9.5 bits of information (3^6 = 729 states).
 * Used for both addresses and operations. Variable-length
 * instructions use 1-3 trytes per operand.
 */
#define TRYTE_SIZE 6
typedef trit tryte[TRYTE_SIZE];

/* Max tryte value: 3^5 + 3^4 + 3^3 + 3^2 + 3 + 1 = 364 */
#define TRYTE_MAX  364
#define TRYTE_MIN  (-364)

/* Convert tryte to integer */
static inline int tryte_to_int(const tryte t) {
    int result = 0;
    int place = 1;
    int i;
    for (i = 0; i < TRYTE_SIZE; i++) {
        result += (int)t[i] * place;
        place *= 3;
    }
    return result;
}

/* Convert integer to tryte (balanced ternary, LSB at [0]) */
static inline void int_to_tryte(int val, tryte t) {
    int i;
    for (i = 0; i < TRYTE_SIZE; i++) t[i] = TRIT_Z;

    int neg = (val < 0);
    if (neg) val = -val;

    for (i = 0; i < TRYTE_SIZE && val > 0; i++) {
        int rem = val % 3;
        val /= 3;
        if (rem == 0) {
            t[i] = TRIT_Z;
        } else if (rem == 1) {
            t[i] = TRIT_P;
        } else {
            t[i] = TRIT_N;
            val++;
        }
    }

    if (neg) {
        for (i = 0; i < TRYTE_SIZE; i++) t[i] = (trit)(-(int)t[i]);
    }
}

/* Add two trytes, result in res */
static inline void tryte_add(const tryte a, const tryte b, tryte res) {
    trit carry = TRIT_Z;
    int i;
    for (i = 0; i < TRYTE_SIZE; i++) {
        int sum = (int)a[i] + (int)b[i] + (int)carry;
        if (sum > 1) {
            carry = TRIT_P;
            res[i] = (trit)(sum - 3);
        } else if (sum < -1) {
            carry = TRIT_N;
            res[i] = (trit)(sum + 3);
        } else {
            carry = TRIT_Z;
            res[i] = (trit)sum;
        }
    }
}

/* Negate a tryte (flip all trits) */
static inline void tryte_neg(const tryte a, tryte res) {
    int i;
    for (i = 0; i < TRYTE_SIZE; i++) {
        res[i] = (trit)(-(int)a[i]);
    }
}

/* Consensus (AND) on two trytes, trit-by-trit */
static inline void tryte_consensus(const tryte a, const tryte b, tryte res) {
    int i;
    for (i = 0; i < TRYTE_SIZE; i++) {
        res[i] = trit_consensus(a[i], b[i]);
    }
}

/* Accept-any (OR) on two trytes, trit-by-trit */
static inline void tryte_accept_any(const tryte a, const tryte b, tryte res) {
    int i;
    for (i = 0; i < TRYTE_SIZE; i++) {
        res[i] = trit_accept_any(a[i], b[i]);
    }
}

/* Compare two trytes: returns -1, 0, or 1 */
static inline int tryte_cmp(const tryte a, const tryte b) {
    /* Compare from MSB to LSB */
    int i;
    for (i = TRYTE_SIZE - 1; i >= 0; i--) {
        if (a[i] > b[i]) return 1;
        if (a[i] < b[i]) return -1;
    }
    return 0;
}

/* Add two trit words (LSB at [0]), result in res */
static inline void trit_word_add(const trit *a, const trit *b, trit *res) {
    trit carry = TRIT_Z;
    int i;
    for (i = 0; i < WORD_SIZE; i++) {
        int sum = (int)a[i] + (int)b[i] + (int)carry;
        if (sum > 1) {
            carry = TRIT_P;
            res[i] = (trit)(sum - 3);
        } else if (sum < -1) {
            carry = TRIT_N;
            res[i] = (trit)(sum + 3);
        } else {
            carry = TRIT_Z;
            res[i] = (trit)sum;
        }
    }
    /* Overflow if carry != 0 — silently truncated to WORD_SIZE */
}

/* Multiply two trit words (schoolbook algorithm), result in res */
static inline void trit_word_mul(const trit *a, const trit *b, trit *res) {
    trit partial[WORD_SIZE];
    trit sum_buf[WORD_SIZE];
    int i, j;

    for (i = 0; i < WORD_SIZE; i++) res[i] = TRIT_Z;

    for (i = 0; i < WORD_SIZE; i++) {
        if (b[i] == TRIT_Z) continue;

        /* Build shifted partial product: a * b[i] << i */
        for (j = 0; j < WORD_SIZE; j++) partial[j] = TRIT_Z;
        for (j = 0; j + i < WORD_SIZE; j++) {
            partial[j + i] = trit_mul(a[j], b[i]);
        }

        /* Accumulate: res += partial */
        trit_word_add(res, partial, sum_buf);
        for (j = 0; j < WORD_SIZE; j++) res[j] = sum_buf[j];
    }
}

/* Negate a trit word (flip all trits) — symmetric balanced ternary */
static inline void trit_word_neg(const trit *a, trit *res) {
    int i;
    for (i = 0; i < WORD_SIZE; i++) {
        res[i] = (trit)(-(int)a[i]);
    }
}

/* Subtract two trit words: res = a - b */
static inline void trit_word_sub(const trit *a, const trit *b, trit *res) {
    trit neg_b[WORD_SIZE];
    trit_word_neg(b, neg_b);
    trit_word_add(a, neg_b, res);
}

/* Consensus (AND) on two trit words, trit-by-trit */
static inline void trit_word_consensus(const trit *a, const trit *b, trit *res) {
    int i;
    for (i = 0; i < WORD_SIZE; i++) {
        res[i] = trit_consensus(a[i], b[i]);
    }
}

/* Accept-any (OR) on two trit words, trit-by-trit */
static inline void trit_word_accept_any(const trit *a, const trit *b, trit *res) {
    int i;
    for (i = 0; i < WORD_SIZE; i++) {
        res[i] = trit_accept_any(a[i], b[i]);
    }
}

/* Convert trit word to integer */
static inline int trit_word_to_int(const trit *w) {
    int result = 0;
    int place = 1;
    int i;
    for (i = 0; i < WORD_SIZE; i++) {
        result += (int)w[i] * place;
        place *= 3;
    }
    return result;
}

/* Convert integer to trit word (balanced ternary, LSB at [0]) */
static inline void int_to_trit_word(int val, trit *w) {
    int i;
    for (i = 0; i < WORD_SIZE; i++) w[i] = TRIT_Z;

    int neg = (val < 0);
    if (neg) val = -val;

    for (i = 0; i < WORD_SIZE && val > 0; i++) {
        int rem = val % 3;
        val /= 3;
        if (rem == 0) {
            w[i] = TRIT_Z;
        } else if (rem == 1) {
            w[i] = TRIT_P;
        } else {
            /* rem == 2: represent as -1 + carry */
            w[i] = TRIT_N;
            val++;
        }
    }

    if (neg) {
        for (i = 0; i < WORD_SIZE; i++) w[i] = (trit)(-(int)w[i]);
    }
}

#endif
