#ifndef SAMSUNG_CN105745888A_CORRELATOR_H
#define SAMSUNG_CN105745888A_CORRELATOR_H

#include <stdint.h>

// Compute correlation between two ternary sequences
// Returns correlation value
int16_t samsung_correlate(uint8_t *seq1, uint8_t *seq2, int len);

#endif