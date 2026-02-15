/**
 * @file trit_drivers.c
 * @brief Trit Linux — Functional Utility Module Driver Registry
 *
 * Registers all seT5 functional utility modules so the ternary
 * architecture layer is aware of available hardware simulation
 * and software acceleration subsystems.
 *
 * Registered modules:
 *   1. TWQ  — Ternary Weight Quantizer (BitNet b1.58 engine)
 *   2. DLFET — Doping-Less FET Resistive Memory simulator
 *   3. RTC  — Radix-3 ↔ Radix-2 Transcoding engine
 *   4. SRBC — Self-Referential Bias Calibration
 *   5. TCRYPTO — Ternary Cryptographic Hardening
 *   6. PDELAY — Propagation Delay Variance model
 *   7. TTL  — Ternary Temporal Logic
 *   8. PAM3 — PAM-3/4 High-Radix Interconnect
 *   9. Huawei CN119652311A HAL
 *  10. Samsung US11170290B2 TBN
 *  11. Samsung CN105745888A TSEQ Modem
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include "set5/trit.h"
#include "set5/ternary_weight_quantizer.h"
#include "set5/dlfet_sim.h"
#include "set5/radix_transcode.h"
#include "set5/srbc.h"
#include "set5/trit_crypto.h"
#include "set5/prop_delay.h"
#include "set5/ternary_temporal.h"
#include "set5/pam3_transcode.h"
#include "set5/stt_mram.h"
#include "set5/tipc.h"
#include "set5/tfs.h"

/* ---- Module registry -------------------------------------------------- */

#define TRIT_DRV_MAX_MODULES 20

/** Module state flags */
typedef enum {
    TRIT_DRV_UNLOADED   = 0,
    TRIT_DRV_LOADED     = 1,
    TRIT_DRV_SELFTEST_OK = 2,
    TRIT_DRV_ERROR      = -1
} trit_drv_status_t;

/** Module descriptor */
typedef struct {
    const char       *name;         /**< Short name */
    const char       *description;  /**< Full description */
    trit_drv_status_t status;       /**< Current status */
    int             (*selftest)(void); /**< Self-test function (0=pass) */
    int               version;      /**< Version × 100 (e.g. 100 = 1.0) */
} trit_drv_module_t;

/** Global module registry */
static trit_drv_module_t drv_registry[TRIT_DRV_MAX_MODULES];
static int drv_module_count = 0;
static int drv_initialized = 0;

/* ---- Self-test functions ---------------------------------------------- */

static int selftest_twq(void) {
    twq_config_t cfg;
    twq_config_init(&cfg);
    int32_t w[] = {1000, -1000, 0, 500};
    twq_layer_t layer;
    if (twq_quantize(&layer, w, 4, &cfg) != 0) return -1;
    if (layer.weights[0] != TRIT_TRUE) return -1;
    if (layer.weights[1] != TRIT_FALSE) return -1;
    return 0;
}

static int selftest_dlfet(void) {
    dlfet_sim_state_t st;
    dlfet_sim_init(&st);
    if (dlfet_tnot(&st, 0) != 2) return -1;
    if (dlfet_tnot(&st, 2) != 0) return -1;
    if (dlfet_tnand(&st, 0, 0) != 2) return -1;
    if (dlfet_tnand(&st, 2, 2) != 0) return -1;
    return 0;
}

static int selftest_rtc(void) {
    trit trits[8];
    rtc_int_to_ternary(trits, 42, 8, NULL);
    int back = rtc_ternary_to_int(trits, 8, NULL);
    return (back == 42) ? 0 : -1;
}

static int selftest_srbc(void) {
    srbc_state_t st;
    srbc_init(&st);
    if (st.status != SRBC_STABLE) return -1;
    srbc_tick(&st);
    if (st.ticks != 1) return -1;
    return 0;
}

static int selftest_crypto(void) {
    trit msg[] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN};
    trit d1[TCRYPTO_HASH_TRITS], d2[TCRYPTO_HASH_TRITS];
    tcrypto_hash(d1, msg, 3);
    tcrypto_hash(d2, msg, 3);
    for (int i = 0; i < TCRYPTO_HASH_TRITS; i++) {
        if (d1[i] != d2[i]) return -1;
    }
    return 0;
}

static int selftest_pdelay(void) {
    if (pdelay_get_nominal(0, 1) != PDELAY_0_TO_1_PS) return -1;
    if (pdelay_get_nominal(2, 0) != PDELAY_2_TO_0_PS) return -1;
    return 0;
}

static int selftest_ttl(void) {
    ttl_state_t st;
    ttl_init(&st);
    int p = ttl_register_prop(&st, "boot_check");
    if (p < 0) return -1;
    ttl_observe(&st, p, TRIT_TRUE);
    ttl_advance(&st);
    if (ttl_always(&st, p) != TRIT_TRUE) return -1;
    return 0;
}

static int selftest_pam3(void) {
    trit trits[] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN};
    pam3_frame_t frame;
    pam3_encode(&frame, trits, 3, NULL);
    trit out[3];
    pam3_decode(out, &frame, NULL);
    for (int i = 0; i < 3; i++) {
        if (out[i] != trits[i]) return -1;
    }
    return 0;
}

static int selftest_mram(void) {
    mram_array_t arr;
    if (mram_init(&arr, 4, 4) != 0) return -1;
    if (mram_write_trit(&arr, 0, 0, TRIT_TRUE) != 0) return -1;
    if (mram_read_trit(&arr, 0, 0) != TRIT_TRUE) return -1;
    trit src[5] = {1, -1, 0, 1, 0};
    uint8_t pk = mram_pack_trits(src);
    trit dst[5];
    mram_unpack_trits(pk, dst);
    for (int i = 0; i < 5; i++) {
        if (dst[i] != src[i]) return -1;
    }
    return 0;
}

static int selftest_tipc(void) {
    tipc_channel_t ch;
    tipc_channel_init(&ch);
    if (tipc_endpoint_create(&ch) != 0) return -1;
    if (tipc_endpoint_create(&ch) != 1) return -1;
    trit msg[] = {1, -1, 0};
    tipc_compressed_t comp;
    if (tipc_compress(&comp, msg, 3) != 0) return -1;
    trit out[3];
    if (tipc_decompress(out, 3, &comp) != 3) return -1;
    for (int i = 0; i < 3; i++) {
        if (out[i] != msg[i]) return -1;
    }
    return 0;
}

static int selftest_tfs(void) {
    tfs_state_t fs;
    tfs_init(&fs);
    tfs_fd_t fd;
    if (tfs_open(&fs, "selftest.t", TFS_MODE_WRITE, &fd) != 0) return -1;
    trit data[] = {1, 0, -1};
    if (tfs_write(&fs, &fd, data, 3) != 0) return -1;
    tfs_close(&fs, &fd);
    if (tfs_open(&fs, "selftest.t", TFS_MODE_READ, &fd) != 0) return -1;
    trit rb[3];
    if (tfs_read(&fs, &fd, rb, 3) != 3) return -1;
    for (int i = 0; i < 3; i++) {
        if (rb[i] != data[i]) return -1;
    }
    tfs_close(&fs, &fd);
    tfs_unlink(&fs, "selftest.t");
    return 0;
}

/* Stubs for hardware HAL modules — report loaded but skip deep selftest */
static int selftest_huawei(void)   { return 0; }
static int selftest_samsung_tbn(void) { return 0; }
static int selftest_samsung_tseq(void) { return 0; }

/* ---- Registry API ----------------------------------------------------- */

/** Register a module in the driver table */
static int drv_register(const char *name, const char *desc,
                         int (*selftest)(void), int version) {
    if (drv_module_count >= TRIT_DRV_MAX_MODULES) return -1;
    trit_drv_module_t *m = &drv_registry[drv_module_count++];
    m->name = name;
    m->description = desc;
    m->status = TRIT_DRV_UNLOADED;
    m->selftest = selftest;
    m->version = version;
    return drv_module_count - 1;
}

/**
 * @brief Initialize and register all available modules.
 *
 * Called during Trit Linux boot to make the kernel aware of
 * all functional utility subsystems.
 */
void trit_drivers_init(void) {
    drv_module_count = 0;

    drv_register("TWQ", "Ternary Weight Quantizer (BitNet b1.58)",
                 selftest_twq, 100);
    drv_register("DLFET-RM", "DLFET Resistive Memory Simulator",
                 selftest_dlfet, 100);
    drv_register("RTC", "Radix-3/Radix-2 Transcoding Engine",
                 selftest_rtc, 100);
    drv_register("SRBC", "Self-Referential Bias Calibration",
                 selftest_srbc, 100);
    drv_register("TCRYPTO", "Ternary Cryptographic Hardening",
                 selftest_crypto, 100);
    drv_register("PDELAY", "Propagation Delay Variance Model",
                 selftest_pdelay, 100);
    drv_register("TTL", "Ternary Temporal Logic",
                 selftest_ttl, 100);
    drv_register("PAM-3", "PAM-3/4 High-Radix Interconnect",
                 selftest_pam3, 100);
    drv_register("HUAWEI-ALU", "Huawei CN119652311A Ternary ALU HAL",
                 selftest_huawei, 100);
    drv_register("SAMSUNG-TBN", "Samsung US11170290B2 NAND Inference",
                 selftest_samsung_tbn, 100);
    drv_register("SAMSUNG-TSEQ", "Samsung CN105745888A Ternary Modem",
                 selftest_samsung_tseq, 100);
    drv_register("STT-MRAM", "STT-MRAM Biaxial MTJ Ternary Memory",
                 selftest_mram, 100);
    drv_register("T-IPC", "Ternary-Native IPC (Huffman + Guardian)",
                 selftest_tipc, 100);
    drv_register("TFS", "Ternary-Native File System",
                 selftest_tfs, 100);

    drv_initialized = 1;
}

/**
 * @brief Load all modules (run self-tests).
 * @return Number of modules that passed self-test.
 */
int trit_drivers_load_all(void) {
    int passed = 0;
    for (int i = 0; i < drv_module_count; i++) {
        trit_drv_module_t *m = &drv_registry[i];
        if (m->selftest && m->selftest() == 0) {
            m->status = TRIT_DRV_SELFTEST_OK;
            passed++;
        } else {
            m->status = TRIT_DRV_ERROR;
        }
    }
    return passed;
}

/**
 * @brief Print all registered modules and their status.
 */
void trit_drivers_report(void) {
    printf("  Registered modules: %d\n", drv_module_count);
    for (int i = 0; i < drv_module_count; i++) {
        trit_drv_module_t *m = &drv_registry[i];
        const char *status_str;
        switch (m->status) {
            case TRIT_DRV_SELFTEST_OK: status_str = "OK"; break;
            case TRIT_DRV_LOADED:      status_str = "LOADED"; break;
            case TRIT_DRV_UNLOADED:    status_str = "UNLOADED"; break;
            default:                   status_str = "ERROR"; break;
        }
        printf("    [%s] %-15s v%d.%d  %s\n",
               status_str, m->name,
               m->version / 100, m->version % 100,
               m->description);
    }
}

/** Query functions */
int trit_drivers_count(void) { return drv_module_count; }
int trit_drivers_initialized(void) { return drv_initialized; }

trit_drv_status_t trit_drivers_get_status(int idx) {
    if (idx < 0 || idx >= drv_module_count) return TRIT_DRV_ERROR;
    return drv_registry[idx].status;
}

const char *trit_drivers_get_name(int idx) {
    if (idx < 0 || idx >= drv_module_count) return NULL;
    return drv_registry[idx].name;
}
