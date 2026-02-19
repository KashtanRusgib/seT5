#include "set5/tipc_compressor.h"

int tipc_compress(uint8_t trits[9], uint8_t *compressed_out, int max_len) {
    int pos = 0;
    for (int i = 0; i < 9; i++) {
        uint8_t t = trits[i];
        if (t == 0) {  // 00 -> 0
            if (pos >= max_len * 8) return -1;
            // bit 0 is 0
            pos++;
        } else if (t == 1) {  // 01 -> 10
            if (pos + 1 >= max_len * 8) return -1;
            compressed_out[pos / 8] |= (1 << (pos % 8));
            pos++;
            // next bit 0
            pos++;
        } else if (t == 2) {  // 10 -> 11
            if (pos + 1 >= max_len * 8) return -1;
            compressed_out[pos / 8] |= (1 << (pos % 8));
            pos++;
            compressed_out[pos / 8] |= (1 << (pos % 8));
            pos++;
        }
    }
    return pos;
}

int tipc_decompress(uint8_t *compressed_in, int bit_count, uint8_t trits_out[9]) {
    int pos = 0;
    int trit_idx = 0;
    while (pos < bit_count && trit_idx < 9) {
        int bit1 = (compressed_in[pos / 8] >> (pos % 8)) & 1;
        pos++;
        if (bit1 == 0) {
            trits_out[trit_idx++] = 0;  // 0 -> 00
        } else {
            if (pos >= bit_count) return -1;  // incomplete
            int bit2 = (compressed_in[pos / 8] >> (pos % 8)) & 1;
            pos++;
            if (bit2 == 0) {
                trits_out[trit_idx++] = 1;  // 10 -> 01
            } else {
                trits_out[trit_idx++] = 2;  // 11 -> 10
            }
        }
    }
    return trit_idx;
}