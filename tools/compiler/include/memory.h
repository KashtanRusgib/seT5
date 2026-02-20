/*
 * memory.h - Ternary Memory Model (TASK-015)
 *
 * Provides a ternary-addressed memory abstraction for the compiler
 * and VM. Addresses are 9-trit balanced ternary words, giving
 * 3^9 = 19683 addressable cells. The physical backing store uses
 * the VM's integer-indexed memory with trit_word address conversion.
 */

#ifndef MEMORY_H
#define MEMORY_H

#include "ternary.h"
#include "vm.h"

/* Ternary address: 9-trit word */
typedef trit_word trit_addr;

/* Convert a ternary address to a flat integer index.
 * Offsets by half the range so negative ternary values map to valid indices.
 * Range: [-9841, +9841] -> [0, 19682] but clamped to MEMORY_SIZE. */
static inline int trit_addr_to_index(const trit_addr addr) {
    int raw = trit_word_to_int(addr);
    /* Shift into non-negative range */
    int idx = raw + (MEMORY_SIZE / 2);
    if (idx < 0) idx = 0;
    if (idx >= MEMORY_SIZE) idx = MEMORY_SIZE - 1;
    return idx;
}

/* Convert a flat integer index back to a ternary address */
static inline void index_to_trit_addr(int idx, trit_addr addr) {
    int raw = idx - (MEMORY_SIZE / 2);
    int_to_trit_word(raw, addr);
}

/* Read from ternary-addressed memory */
static inline int tmem_read(const trit_addr addr) {
    return vm_memory_read(trit_addr_to_index(addr));
}

/* Write to ternary-addressed memory */
static inline void tmem_write(const trit_addr addr, int value) {
    vm_memory_write(trit_addr_to_index(addr), value);
}

#endif /* MEMORY_H */
