#ifndef TIPC_COMPRESSOR_H
#define TIPC_COMPRESSOR_H

#include <stdint.h>

// Compress 9 trits (each 2 bits) to bitstream
// Returns bit count, output in compressed_out
int tipc_compress(uint8_t trits[9], uint8_t *compressed_out, int max_len);

// Decompress bitstream to 9 trits
int tipc_decompress(uint8_t *compressed_in, int bit_count, uint8_t trits_out[9]);

#endif