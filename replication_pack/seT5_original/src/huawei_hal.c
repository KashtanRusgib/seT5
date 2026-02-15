/**
 * @file huawei_hal.c
 * @brief Hardware Abstraction Layer for Huawei CN119652311A Ternary Chip
 *
 * Provides detection, initialisation, and low-level access to the
 * Huawei ternary chip described in patent CN119652311A.
 *
 * When real hardware is present (MMIO aperture detected), the HAL
 * communicates via memory-mapped registers.  Otherwise it falls
 * back to cycle-accurate software emulation of the patent circuits,
 * allowing seT5 to develop and test on any platform.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/huawei_cn119652311a.h"
#include "set5/huawei_mmio.h"
#include <string.h>

/* ===================================================================== */
/* Hardware Detection                                                    */
/* ===================================================================== */

/**
 * Attempt to detect real Huawei ternary silicon by reading the chip
 * ID register at the expected MMIO base address.
 *
 * On hosted/emulated builds (Linux userspace, QEMU without ternary
 * device model), this always returns 0 (no hardware).
 */
static int hw_detect_silicon(hw_hal_state_t *state)
{
#if defined(HW_FORCE_EMULATED)
    /* Build-time override: always emulate */
    (void)state;
    return 0;
#elif defined(__linux__) && !defined(__KERNEL__)
    /*
     * Userspace: We could mmap /dev/mem or a UIO device.
     * For now, assume no real silicon in userspace builds.
     */
    (void)state;
    return 0;
#elif defined(__KERNEL__)
    /*
     * Kernel build: ioremap the MMIO aperture and probe.
     * This is a stub — real implementation would use the
     * platform bus / device tree to discover the chip.
     */
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
 * All features are "present" since we model them in software.
 */
static void hw_populate_emulated_caps(hw_chip_caps_t *caps)
{
    memset(caps, 0, sizeof(*caps));

    caps->chip_id      = HW_CHIP_ID_EXPECTED;
    caps->patent_class = 0x49;  /* G06F7/49 */

    caps->has_inc_gate    = 1;
    caps->has_dec_gate    = 1;
    caps->has_half_adder  = 1;
    caps->has_full_adder  = 1;
    caps->has_multiplier  = 1;
    caps->has_approx_mul  = 1;
    caps->has_compensation = 1;

    /* Default electrical parameters (patent typical values) */
    caps->vdd_mv    = 1000;   /* 1.0 V */
    caps->vth_lvt_mv = 250;   /* 0.25 V */
    caps->vth_mvt_mv = 400;   /* 0.40 V */
    caps->vth_hvt_mv = 650;   /* 0.65 V */

    /* Emulated scale */
    caps->max_trit_width = 32;
    caps->mul_width      = 6;   /* Up to 6trit×6trit natively */
    caps->num_alu_units  = 1;
}

/* ===================================================================== */
/* MMIO Capability Population                                            */
/* ===================================================================== */

/**
 * Read capabilities from real hardware via MMIO registers.
 */
static void hw_populate_mmio_caps(hw_hal_state_t *state)
{
    volatile uint32_t *base = state->mmio_base;

    state->caps.chip_id = hw_mmio_read(base, HW_REG_CHIP_ID);

    uint32_t feat = hw_mmio_read(base, HW_REG_FEATURES);
    state->caps.has_inc_gate      = !!(feat & HW_FEAT_INC_GATE);
    state->caps.has_dec_gate      = !!(feat & HW_FEAT_DEC_GATE);
    state->caps.has_half_adder    = !!(feat & HW_FEAT_HALF_ADDER);
    state->caps.has_full_adder    = !!(feat & HW_FEAT_FULL_ADDER);
    state->caps.has_multiplier    = !!(feat & HW_FEAT_MULTIPLIER);
    state->caps.has_approx_mul    = !!(feat & HW_FEAT_APPROX_MUL);
    state->caps.has_compensation  = !!(feat & (HW_FEAT_COMP_PLUS6 |
                                               HW_FEAT_COMP_PLUS9));

    uint32_t vdd = hw_mmio_read(base, HW_REG_VDD_CTRL);
    state->caps.vdd_mv = (int)(vdd & 0xFFFF);

    uint32_t vth = hw_mmio_read(base, HW_REG_VTH_CTRL);
    state->caps.vth_lvt_mv = (int)(HW_VTH_LVT(vth) * 10);
    state->caps.vth_mvt_mv = (int)(HW_VTH_MVT(vth) * 10);
    state->caps.vth_hvt_mv = (int)(HW_VTH_HVT(vth) * 10);

    /* Trit width depends on revision */
    state->caps.max_trit_width = 32;
    state->caps.mul_width      = (feat & HW_FEAT_WIDE_MUL) ? 6 : 2;
    state->caps.num_alu_units  = 1;
}

/* ===================================================================== */
/* Public API                                                            */
/* ===================================================================== */

int hw_hal_init(hw_hal_state_t *state)
{
    if (!state) return -1;
    memset(state, 0, sizeof(*state));

    if (hw_detect_silicon(state)) {
        /* Real hardware found */
        state->mode = HW_MODE_MMIO;
        hw_populate_mmio_caps(state);
    } else {
        /* Fallback to software emulation */
        state->mode = HW_MODE_EMULATED;
        hw_populate_emulated_caps(&state->caps);
    }

    state->initialized = 1;
    return 0;
}

int hw_hal_shutdown(hw_hal_state_t *state)
{
    if (!state) return -1;

    if (state->mode == HW_MODE_MMIO && state->mmio_base) {
        /* In a real kernel, iounmap here */
        state->mmio_base = NULL;
    }

    state->initialized = 0;
    return 0;
}
