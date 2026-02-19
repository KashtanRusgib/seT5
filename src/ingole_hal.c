/**
 * @file ingole_hal.c
 * @brief Hardware Abstraction Layer for WO2016199157A1 Ternary ALU (TALU)
 *
 * Provides detection, initialisation, and capability query for the
 * TALU described in patent WO2016199157A1.
 *
 * When real hardware is present (MMIO aperture detected), the HAL
 * communicates via memory-mapped registers.  Otherwise it falls
 * back to software emulation of the patent circuits, allowing seT5
 * to develop and test on any platform.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/ingole_talu.h"
#include <string.h>

/* ===================================================================== */
/* Hardware Detection                                                    */
/* ===================================================================== */

/**
 * Attempt to detect real Ingole TALU silicon by reading the chip ID
 * register at the expected MMIO base address.
 *
 * On hosted/emulated builds, this always returns 0 (no hardware).
 */
static int ig_detect_silicon(ig_hal_state_t *state)
{
#if defined(IG_FORCE_EMULATED)
    (void)state;
    return 0;
#elif defined(__linux__) && !defined(__KERNEL__)
    (void)state;
    return 0;
#elif defined(__KERNEL__)
    (void)state;
    return 0;
#else
    (void)state;
    return 0;
#endif
}

/* ===================================================================== */
/* Emulated Capability Population                                        */
/* ===================================================================== */

/**
 * Populate capabilities for software-emulated mode.
 * All TALU features are "present" since we model them in software.
 */
static void ig_populate_emulated_caps(ig_chip_caps_t *caps)
{
    memset(caps, 0, sizeof(*caps));

    caps->chip_id      = IG_CHIP_ID_EXPECTED;
    caps->patent_class = 0x49;  /* G06F7/49 */

    /* All gates available in emulation */
    caps->has_tnot        = 1;
    caps->has_cwc         = 1;
    caps->has_ccwc        = 1;
    caps->has_add1carry   = 1;
    caps->has_tand        = 1;
    caps->has_tnand       = 1;
    caps->has_tor         = 1;
    caps->has_tnor        = 1;
    caps->has_xtor        = 1;
    caps->has_comparator  = 1;
    caps->has_half_adder  = 1;
    caps->has_full_adder  = 1;
    caps->has_decoder     = 1;
    caps->has_parity      = 1;

    /* Arithmetic */
    caps->has_add     = 1;
    caps->has_sub_ab  = 1;
    caps->has_sub_ba  = 1;

    /* All inclusive */
    caps->has_ai_tand = 1;
    caps->has_ai_tor  = 1;

    /* Flags */
    caps->has_all_zero    = 1;
    caps->has_overflow    = 1;
    caps->has_even_parity = 1;
}

/* ===================================================================== */
/* Public API                                                            */
/* ===================================================================== */

int ig_hal_init(ig_hal_state_t *state)
{
    if (!state) return -1;

    memset(state, 0, sizeof(*state));
    state->max_trit_width = 32;

    if (ig_detect_silicon(state)) {
        state->is_mmio  = 1;
        state->chip_id  = IG_CHIP_ID_EXPECTED;
        /* Real silicon: mmio_base would be set by ioremap */
    } else {
        state->is_mmio  = 0;
        state->chip_id  = IG_CHIP_ID_EXPECTED;
        state->mmio_base = (volatile uint32_t *)0;
    }

    return 0;
}

void ig_hal_caps(const ig_hal_state_t *state, ig_chip_caps_t *caps)
{
    if (!state || !caps) return;

    if (state->is_mmio) {
        /* Read capabilities from hardware registers — stub */
        ig_populate_emulated_caps(caps);
    } else {
        ig_populate_emulated_caps(caps);
    }
}

void ig_hal_shutdown(ig_hal_state_t *state)
{
    if (!state) return;

    if (state->is_mmio) {
        /* Unmap MMIO — stub */
    }
    memset(state, 0, sizeof(*state));
}
