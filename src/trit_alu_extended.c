/**
 * @file trit_alu_extended.c
 * @brief Extended ternary ALU operations for test batch 5352-5401
 *
 * Provides implementations of advanced ternary operations tested in batch 5352-5401.
 * These are minimal stub implementations for testing purposes.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdlib.h>
#include <string.h>
#include "set5/trit.h"

/* Basic arithmetic helpers */
trit trit_add(trit a, trit b, trit *carry) {
    if (!carry) return TRIT_UNKNOWN;
    int sum = (int)a + (int)b + (int)*carry;
    *carry = (sum > 1) ? TRIT_TRUE : ((sum < -1) ? TRIT_FALSE : TRIT_UNKNOWN);
    if (sum > 1) sum -= 3;
    if (sum < -1) sum += 3;
    return (trit)sum;
}

trit trit_sub(trit a, trit b, trit *borrow) {
    if (!borrow) return TRIT_UNKNOWN;
    int diff = (int)a - (int)b - (int)*borrow;
    *borrow = (diff < -1) ? TRIT_TRUE : TRIT_UNKNOWN;
    if (diff < -1) diff += 3;
    if (diff > 1) diff -= 3;
    return (trit)diff;
}

trit trit_mul(trit a, trit b) {
    return (trit)((int)a * (int)b);
}

trit trit_div(trit a, trit b) {
    if (b == TRIT_UNKNOWN || b == 0) return TRIT_UNKNOWN;
    return (trit)((int)a / (int)b);
}

trit trit_mod(trit a, trit b) {
    if (b == TRIT_UNKNOWN || b == 0) return TRIT_UNKNOWN;
    return (trit)((int)a % 3);
}

/* Shift/rotate operations */
trit trit_shift_left(trit *val, int len) {
    if (!val || len <= 0) return TRIT_UNKNOWN;
    trit carry = val[len-1];
    for (int i = len-1; i > 0; i--) val[i] = val[i-1];
    val[0] = TRIT_UNKNOWN;
    return carry;
}

void trit_shift_right_arithmetic(trit *val, int len) {
    if (!val || len <= 0) return;
    trit sign = val[len-1];
    for (int i = 0; i < len-1; i++) val[i] = val[i+1];
    val[len-1] = sign;
}

void trit_rotate_left(trit *val, int len) {
    if (!val || len <= 0) return;
    trit temp = val[len-1];
    for (int i = len-1; i > 0; i--) val[i] = val[i-1];
    val[0] = temp;
}

/* Comparison and logic */
trit trit_compare(trit a, trit b) {
    if (a == b) return TRIT_UNKNOWN;
    return (a > b) ? TRIT_TRUE : TRIT_FALSE;
}

trit trit_min(trit a, trit b) {
    return (a < b) ? a : b;
}

trit trit_max(trit a, trit b) {
    return (a > b) ? a : b;
}

trit trit_abs(trit a) {
    return (a == TRIT_FALSE) ? TRIT_TRUE : a;
}

trit trit_negate(trit a) {
    return (trit)(-(int)a);
}

trit trit_increment(trit a) {
    int val = (int)a + 1;
    if (val > 1) val = -1;
    return (trit)val;
}

trit trit_decrement(trit a) {
    int val = (int)a - 1;
    if (val < -1) val = 1;
    return (trit)val;
}

/* Logical operations */
trit trit_xor(trit a, trit b) {
    return (a == b) ? TRIT_FALSE : TRIT_TRUE;
}

trit trit_nand(trit a, trit b) {
    return trit_negate(trit_and(a, b));
}

trit trit_nor(trit a, trit b) {
    return trit_negate(trit_or(a, b));
}

/* Word operations */
void trit_word_add(trit *result, const trit *a, const trit *b, int len) {
    if (!result || !a || !b || len <= 0) return;
    trit carry = TRIT_UNKNOWN;
    for (int i = 0; i < len; i++) {
        result[i] = trit_add(a[i], b[i], &carry);
    }
}

void trit_word_sub(trit *result, const trit *a, const trit *b, int len) {
    if (!result || !a || !b || len <= 0) return;
    trit borrow = TRIT_UNKNOWN;
    for (int i = 0; i < len; i++) {
        result[i] = trit_sub(a[i], b[i], &borrow);
    }
}

trit trit_dot_product(const trit *a, const trit *b, int len) {
    if (!a || !b || len <= 0) return TRIT_UNKNOWN;
    int sum = 0;
    for (int i = 0; i < len; i++) {
        sum += (int)a[i] * (int)b[i];
    }
    return (trit)(sum % 3);
}

/* Utility functions */
trit trit_parity(const trit *word, int len) {
    if (!word || len <= 0) return TRIT_UNKNOWN;
    int sum = 0;
    for (int i = 0; i < len; i++) sum += (int)word[i];
    return (trit)(sum % 3);
}

trit trit_checksum(const trit *data, int len) {
    return trit_parity(data, len);
}

uint32_t trit_hash(const trit *data, int len) {
    if (!data || len <= 0) return 0;
    uint32_t hash = 5381;
    for (int i = 0; i < len; i++) {
        hash = ((hash << 5) + hash) + (uint32_t)data[i];
    }
    return hash;
}

int trit_popcount_positive(const trit *word, int len) {
    if (!word || len <= 0) return 0;
    int count = 0;
    for (int i = 0; i < len; i++) {
        if (word[i] == TRIT_TRUE) count++;
    }
    return count;
}

int trit_clz(const trit *word, int len) {
    if (!word || len <= 0) return 0;
    int count = 0;
    for (int i = len-1; i >= 0; i--) {
        if (word[i] == TRIT_UNKNOWN) count++;
        else break;
    }
    return count;
}

int trit_ctz(const trit *word, int len) {
    if (!word || len <= 0) return 0;
    int count = 0;
    for (int i = 0; i < len; i++) {
        if (word[i] == TRIT_UNKNOWN) count++;
        else break;
    }
    return count;
}

void trit_reverse(trit *dest, const trit *src, int len) {
    if (!dest || !src || len <= 0) return;
    for (int i = 0; i < len; i++) {
        dest[i] = src[len - 1 - i];
    }
}

/* Saturating arithmetic */
trit trit_add_saturate(trit a, trit b) {
    int sum = (int)a + (int)b;
    if (sum > 1) return TRIT_TRUE;
    if (sum < -1) return TRIT_FALSE;
    return (trit)sum;
}

trit trit_sub_saturate(trit a, trit b) {
    int diff = (int)a - (int)b;
    if (diff > 1) return TRIT_TRUE;
    if (diff < -1) return TRIT_FALSE;
    return (trit)diff;
}

/* Conditional operations */
trit trit_cmov(trit condition, trit val_true, trit val_false) {
    if (condition == TRIT_TRUE) return val_true;
    if (condition == TRIT_FALSE) return val_false;
    return TRIT_UNKNOWN;
}

void trit_barrel_shift(trit *word, int len, int amount) {
    if (!word || len <= 0 || amount <= 0) return;
    for (int i = 0; i < amount; i++) {
        trit_shift_left(word, len);
    }
}

int trit_priority_encode(const trit *word, int len) {
    if (!word || len <= 0) return -1;
    for (int i = 0; i < len; i++) {
        if (word[i] == TRIT_TRUE) return i;
    }
    return -1;
}

trit trit_mux(const trit *inputs, trit select) {
    if (!inputs) return TRIT_UNKNOWN;
    int idx = (int)select + 1;  /* Map -1,0,+1 to 0,1,2 */
    if (idx < 0 || idx > 2) return TRIT_UNKNOWN;
    return inputs[idx];
}

void trit_demux(trit *outputs, trit input, trit select) {
    if (!outputs) return;
    int idx = (int)select + 1;
    outputs[0] = (idx == 0) ? input : TRIT_UNKNOWN;
    outputs[1] = (idx == 1) ? input : TRIT_UNKNOWN;
    outputs[2] = (idx == 2) ? input : TRIT_UNKNOWN;
}
