#ifndef MULTI_RADIX_UNIT_H
#define MULTI_RADIX_UNIT_H

#include <stdint.h>

#define RADIX3 3
#define RADIX4 4
#define RADIX6 6

int16_t multi_radix_add(int16_t a, int16_t b, int radix);
void multi_radix_fft(int16_t *data, int size);

#endif