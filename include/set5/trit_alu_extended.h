/**
 * @file trit_alu_extended.h
 * @brief Extended ternary ALU operations for test batch 5352-5401
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef TRIT_ALU_EXTENDED_H
#define TRIT_ALU_EXTENDED_H

#include "trit.h"
#include <stdint.h>

/* Arithmetic with carry/borrow */
trit trit_add(trit a, trit b, trit *carry);
trit trit_sub(trit a, trit b, trit *borrow);
trit trit_mul(trit a, trit b);
trit trit_div(trit a, trit b);
trit trit_mod(trit a, trit b);

/* Shift and rotate */
trit trit_shift_left(trit *val, int len);
void trit_shift_right_arithmetic(trit *val, int len);
void trit_rotate_left(trit *val, int len);

/* Comparison */
trit trit_compare(trit a, trit b);
trit trit_min(trit a, trit b);
trit trit_max(trit a, trit b);
trit trit_abs(trit a);
trit trit_negate(trit a);
trit trit_increment(trit a);
trit trit_decrement(trit a);

/* Logic */
trit trit_xor(trit a, trit b);
trit trit_nand(trit a, trit b);
trit trit_nor(trit a, trit b);

/* Word operations */
void trit_word_add(trit *result, const trit *a, const trit *b, int len);
void trit_word_sub(trit *result, const trit *a, const trit *b, int len);
trit trit_dot_product(const trit *a, const trit *b, int len);

/* Utility */
trit trit_parity(const trit *word, int len);
trit trit_checksum(const trit *data, int len);
uint32_t trit_hash(const trit *data, int len);
int trit_popcount_positive(const trit *word, int len);
int trit_clz(const trit *word, int len);
int trit_ctz(const trit *word, int len);
void trit_reverse(trit *dest, const trit *src, int len);

/* Saturating arithmetic */
trit trit_add_saturate(trit a, trit b);
trit trit_sub_saturate(trit a, trit b);

/* Conditional */
trit trit_cmov(trit condition, trit val_true, trit val_false);

/* Advanced */
void trit_barrel_shift(trit *word, int len, int amount);
int trit_priority_encode(const trit *word, int len);
trit trit_mux(const trit *inputs, trit select);
void trit_demux(trit *outputs, trit input, trit select);

#endif /* TRIT_ALU_EXTENDED_H */
