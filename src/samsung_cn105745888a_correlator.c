#include "set5/samsung_cn105745888a_correlator.h"

// Ternary to int: 0->0, 1->1, 2->-1
static int trit_to_int(uint8_t t) {
    if (t == 0) return 0;
    if (t == 1) return 1;
    return -1;
}

int16_t samsung_correlate(uint8_t *seq1, uint8_t *seq2, int len) {
    int16_t sum = 0;
    for (int i = 0; i < len; i++) {
        int a = trit_to_int(seq1[i]);
        int b = trit_to_int(seq2[i]);
        sum += a * b;
    }
    return sum;
}