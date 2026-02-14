/**
 * @file samsung_hal.c
 * @brief Hardware Abstraction Layer for Samsung US11170290B2 NAND Inference
 *
 * Provides detection, initialisation, mode configuration, and low-level
 * access to the Samsung NAND in-memory neural network inference chip
 * described in patent US11170290B2.
 *
 * When real hardware is present (MMIO aperture detected), the HAL
 * communicates via memory-mapped registers.  Otherwise it falls back
 * to software emulation, allowing seT5 to develop and test on any
 * platform.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/samsung_us11170290b2.h"
#include "set5/samsung_nand.h"
#include <string.h>

/* ===================================================================== */
/* Hardware Detection                                                    */
/* ===================================================================== */

/**
 * Attempt to detect real Samsung NAND inference silicon by probing
 * the chip ID register at the expected MMIO base address.
 */
static int ss_detect_silicon(ss_hal_state_t *state)
{
#if defined(SS_FORCE_EMULATED)
    (void)state;
    return 0;
#elif defined(__linux__) && !defined(__KERNEL__)
    /*
     * Userspace: could mmap a UIO device or /dev/mem.
     * For now, assume no real silicon in userspace builds.
     */
    (void)state;
    return 0;
#elif defined(__KERNEL__)
    /*
     * Kernel: ioremap MMIO and probe chip ID.
     * Stub — real implementation would use platform bus / DT.
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
static void ss_populate_emulated_caps(ss_chip_caps_t *caps)
{
    memset(caps, 0, sizeof(*caps));

    caps->chip_id       = SS_CHIP_ID_EXPECTED;
    caps->patent_class  = 0x5443;  /* G06F7/5443 */

    /* Network modes */
    caps->has_bnn  = 1;
    caps->has_tbn  = 1;
    caps->has_zid  = 1;

    /* Emulated NAND topology: modest defaults */
    caps->num_planes            = 2;
    caps->num_blocks_per_plane  = 4;
    caps->num_strings_per_block = 64;
    caps->num_wl_pairs_per_string = 64;

    /* Parallelism */
    caps->sa_bits                = 4;  /* 4-bit multi-bit SA */
    caps->max_concurrent_blocks  = 4;
    caps->supports_plane_pipeline = 1;

    /* Counter/accumulator */
    caps->counter_bits    = 16;
    caps->max_vector_size = 64;

    /* Electrical (typical NAND values) */
    caps->vread_mv  = 500;    /* 0.5 V */
    caps->vpass_mv  = 7000;   /* 7.0 V */
}

/* ===================================================================== */
/* MMIO Capability Population                                            */
/* ===================================================================== */

/**
 * Read capabilities from real hardware via MMIO registers.
 */
static void ss_populate_mmio_caps(ss_hal_state_t *state)
{
    if (!state->mmio_base)
        return;

    uint32_t features = ss_mmio_read(state->mmio_base, SS_REG_FEATURES);
    uint32_t topo     = ss_mmio_read(state->mmio_base, SS_REG_TOPOLOGY);

    state->caps.chip_id = ss_mmio_read(state->mmio_base, SS_REG_CHIP_ID);

    state->caps.has_bnn = !!(features & SS_FEAT_BNN);
    state->caps.has_tbn = !!(features & SS_FEAT_TBN);
    state->caps.has_zid = !!(features & SS_FEAT_ZID);

    state->caps.num_planes            = SS_TOPO_PLANES(topo);
    state->caps.num_blocks_per_plane  = SS_TOPO_BLOCKS(topo);
    state->caps.num_strings_per_block = SS_TOPO_STRINGS(topo);
    state->caps.num_wl_pairs_per_string = SS_TOPO_SYNAPSES(topo);

    state->caps.max_concurrent_blocks = (features & SS_FEAT_MULTI_BLOCK) ? 4 : 1;
    state->caps.supports_plane_pipeline = !!(features & SS_FEAT_PIPELINE);

    uint32_t sa_cfg = ss_mmio_read(state->mmio_base, SS_REG_SA_CONFIG);
    state->caps.sa_bits = (int)(sa_cfg & 0xF);
    if (state->caps.sa_bits == 0) state->caps.sa_bits = 1;

    state->caps.counter_bits    = 16;
    state->caps.max_vector_size = state->caps.num_wl_pairs_per_string;

    /* Read electrical params if available (default to emulated) */
    state->caps.vread_mv  = 500;
    state->caps.vpass_mv  = 7000;
}

/* ===================================================================== */
/* HAL Lifecycle                                                         */
/* ===================================================================== */

int ss_hal_init(ss_hal_state_t *state)
{
    if (!state)
        return -1;

    memset(state, 0, sizeof(*state));

    if (ss_detect_silicon(state)) {
        /* Real hardware found */
        state->mode = SS_MODE_MMIO;
        ss_populate_mmio_caps(state);
    } else {
        /* Fall back to emulation */
        state->mode = SS_MODE_EMULATED;
        state->mmio_base = NULL;
        ss_populate_emulated_caps(&state->caps);
    }

    /* Default to TBN mode (superset of BNN) */
    state->net_mode    = SS_MODE_TBN;
    state->par_level   = SS_PAR_SEQUENTIAL;
    state->zid_enabled = 1;  /* Auto-enable ZID in TBN mode */
    state->initialized = 1;

    return 0;
}

int ss_hal_shutdown(ss_hal_state_t *state)
{
    if (!state)
        return -1;

    state->initialized = 0;
    state->mmio_base   = NULL;
    memset(&state->caps, 0, sizeof(state->caps));

    return 0;
}

int ss_hal_set_mode(ss_hal_state_t *state, ss_network_mode_t mode)
{
    if (!state || !state->initialized)
        return -1;

    state->net_mode = mode;

    /* Auto-enable/disable ZID based on mode */
    if (mode == SS_MODE_TBN && state->caps.has_zid) {
        state->zid_enabled = 1;
    } else {
        state->zid_enabled = 0;
    }

    /* Update hardware mode register if using MMIO */
    if (state->mode == SS_MODE_MMIO && state->mmio_base) {
        uint32_t reg = ss_mmio_read(state->mmio_base, SS_REG_MODE);
        if (mode == SS_MODE_TBN) {
            reg |= SS_MODE_BIT_TBN;
            reg |= SS_MODE_BIT_ZID_ENB;
        } else {
            reg &= ~SS_MODE_BIT_TBN;
            reg &= ~SS_MODE_BIT_ZID_ENB;
        }
        ss_mmio_write(state->mmio_base, SS_REG_MODE, reg);
    }

    return 0;
}

int ss_hal_set_parallelism(ss_hal_state_t *state, ss_parallelism_t level)
{
    if (!state || !state->initialized)
        return -1;

    /* Validate support */
    switch (level) {
    case SS_PAR_MULTI_BLOCK:
        if (state->caps.max_concurrent_blocks < 2) return -1;
        break;
    case SS_PAR_MULTI_PLANE:
        if (state->caps.num_planes < 2) return -1;
        break;
    case SS_PAR_PIPELINED:
        if (!state->caps.supports_plane_pipeline) return -1;
        break;
    case SS_PAR_SEQUENTIAL:
    default:
        break;
    }

    state->par_level = level;

    /* Update hardware register if using MMIO */
    if (state->mode == SS_MODE_MMIO && state->mmio_base) {
        uint32_t reg = ss_mmio_read(state->mmio_base, SS_REG_MODE);
        reg &= ~SS_MODE_PAR_MASK;
        reg |= ((uint32_t)level << SS_MODE_PAR_SHIFT) & SS_MODE_PAR_MASK;
        ss_mmio_write(state->mmio_base, SS_REG_MODE, reg);
    }

    return 0;
}
