#ifndef CODEGEN_H
#define CODEGEN_H

#include <stddef.h>

#define MAX_BYTECODE 1024

extern unsigned char bytecode[MAX_BYTECODE];
extern size_t bc_idx;

void codegen(void);

#endif
