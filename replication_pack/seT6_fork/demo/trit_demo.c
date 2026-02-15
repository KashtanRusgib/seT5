/*
 * seT6 Phase 1 Demo — Ternary Logic on Binary Hardware
 * Build: gcc -std=c99 -O2 -I../include -o trit_demo trit_demo.c
 *
 * SPDX-License-Identifier: GPL-2.0
 */
#pragma ternary

#include <stdio.h>
#include "set6/trit.h"

static const char *trit_str(trit v) {
    switch (v) {
    case TRIT_FALSE:   return "F(-1)";
    case TRIT_UNKNOWN: return "U( 0)";
    case TRIT_TRUE:    return "T(+1)";
    default:           return "!ERR!";
    }
}

/* Simulate an seL4-style capability check with ternary auth */
static trit capability_check(trit has_cap, trit cap_valid) {
    /* Access granted only if we have the cap AND it's valid */
    return trit_and(has_cap, cap_valid);
}

int main(void) {
    printf("=== seT6 Ternary Logic Demo ===\n\n");

    /* Truth table: Kleene AND */
    printf("Kleene AND truth table:\n");
    trit vals[] = { TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE };
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++)
            printf("  %s AND %s = %s\n",
                   trit_str(vals[i]), trit_str(vals[j]),
                   trit_str(trit_and(vals[i], vals[j])));

    printf("\nKleene NOT:\n");
    for (int i = 0; i < 3; i++)
        printf("  NOT %s = %s\n",
               trit_str(vals[i]), trit_str(trit_not(vals[i])));

    /* Capability check scenarios */
    printf("\nCapability check (AND):\n");
    printf("  has_cap=T, valid=T  -> %s  (GRANT)\n",
           trit_str(capability_check(TRIT_TRUE, TRIT_TRUE)));
    printf("  has_cap=T, valid=U  -> %s  (DEFER — unknown validity)\n",
           trit_str(capability_check(TRIT_TRUE, TRIT_UNKNOWN)));
    printf("  has_cap=T, valid=F  -> %s  (DENY)\n",
           trit_str(capability_check(TRIT_TRUE, TRIT_FALSE)));
    printf("  has_cap=U, valid=T  -> %s  (DEFER — unknown possession)\n",
           trit_str(capability_check(TRIT_UNKNOWN, TRIT_TRUE)));

    /* Safe collapse for branching */
    trit result = capability_check(TRIT_TRUE, TRIT_UNKNOWN);
    if (trit_to_bool_safe(result)) {
        printf("\nAccess granted (safe collapse).\n");
    } else {
        printf("\nAccess conservatively denied (unknown -> false).\n");
    }

    /* Packed SIMD demo */
    printf("\nPacked SIMD (32 trits in uint64):\n");
    uint64_t a = 0x5555555555555555ULL; /* all +1 */
    uint64_t b = 0x0000000000000000ULL; /* all  0 (unknown) */
    uint64_t r = trit_and_packed64(a, b);
    printf("  all-true AND all-unknown = 0x%016llx (expect all-unknown: 0x0)\n",
           (unsigned long long)r);

    return 0;
}
