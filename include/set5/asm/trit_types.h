#ifndef ASM_TRIT_TYPES_H
#define ASM_TRIT_TYPES_H

#include <stdint.h>

typedef int8_t trit_t;
typedef struct {
    trit_t high;
    trit_t low;
} trit2_t;
typedef uint32_t trit_word_t;

static inline trit2_t trit_to_trit2(trit_t t) {
    trit2_t res;
    res.low = t;
    res.high = 0;
    return res;
}

static inline trit_t trit2_to_trit(trit2_t t2) {
    return t2.low; // or some combination, but simple
}

#endif // ASM_TRIT_TYPES_H