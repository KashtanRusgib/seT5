#ifndef TERNARY_WALLACE_TREE_H
#define TERNARY_WALLACE_TREE_H

#include <stdint.h>

// Ternary trit encoding: 0=unknown, 1=true(+1), 2=false(-1)
typedef uint8_t trit_t;

#define TRIT_UNKNOWN 0
#define TRIT_TRUE 1
#define TRIT_FALSE 2

// Multiply two ternary numbers using Wallace tree
int16_t ternary_wallace_multiply(int16_t a, int16_t b);

#endif