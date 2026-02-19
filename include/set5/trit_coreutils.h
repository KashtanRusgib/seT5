/**
 * @file trit_coreutils.h
 * @brief seT5 — Trit Core Utilities (inline implementation)
 *
 * Provides sorting, searching, merging, and filtering utilities for trit arrays.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET5_TRIT_COREUTILS_H
#define SET5_TRIT_COREUTILS_H

#include <stdint.h>
#include <string.h>
#include "set5/trit.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Types ============================================================= */

typedef struct {
    trit *data;
    int size;
} trit_array_t;

/* ==== Functions ========================================================= */

static inline void trit_sort(trit_array_t *arr) {
    if (!arr || !arr->data || arr->size <= 1) return;
    // Simple bubble sort
    for (int i = 0; i < arr->size - 1; i++) {
        for (int j = 0; j < arr->size - i - 1; j++) {
            if (arr->data[j] > arr->data[j + 1]) {
                trit temp = arr->data[j];
                arr->data[j] = arr->data[j + 1];
                arr->data[j + 1] = temp;
            }
        }
    }
}

static inline int trit_search(trit_array_t *arr, trit value) {
    if (!arr || !arr->data) return -1;
    for (int i = 0; i < arr->size; i++) {
        if (arr->data[i] == value) return i;
    }
    return -1;
}

static inline void trit_merge(trit_array_t *dest, trit_array_t *src1, trit_array_t *src2) {
    if (!dest || !src1 || !src2) return;
    int i = 0, j = 0, k = 0;
    while (i < src1->size && j < src2->size) {
        if (src1->data[i] <= src2->data[j]) {
            dest->data[k++] = src1->data[i++];
        } else {
            dest->data[k++] = src2->data[j++];
        }
    }
    while (i < src1->size) dest->data[k++] = src1->data[i++];
    while (j < src2->size) dest->data[k++] = src2->data[j++];
    dest->size = k;
}

static inline void trit_filter(trit_array_t *arr, trit condition) {
    if (!arr || !arr->data) return;
    int j = 0;
    for (int i = 0; i < arr->size; i++) {
        if (arr->data[i] == condition) {
            arr->data[j++] = arr->data[i];
        }
    }
    arr->size = j;
}

#ifdef __cplusplus
}
#endif

#endif /* SET5_TRIT_COREUTILS_H */