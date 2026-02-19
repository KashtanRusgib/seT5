#ifndef TERNARY_SENSE_AMP_H
#define TERNARY_SENSE_AMP_H

#include <stdint.h>

// Sense amplifier for ternary MRAM
// Returns trit: 0=low, 1=mid, 2=high
uint8_t ternary_sense_amp_read(uint8_t bitline_current);

#endif