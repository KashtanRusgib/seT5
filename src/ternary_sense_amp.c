#include "set5/ternary_sense_amp.h"

#define TH_LOW 10
#define TH_HIGH 50

uint8_t ternary_sense_amp_read(uint8_t bitline_current) {
    if (bitline_current < TH_LOW) return 0;
    if (bitline_current < TH_HIGH) return 1;
    return 2;
}