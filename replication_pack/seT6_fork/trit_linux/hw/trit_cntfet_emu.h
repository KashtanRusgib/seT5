/**
 * @file trit_cntfet_emu.h
 * @brief seT6 Carbon-Nanotube FET (CNTFET) Ternary Gate Emulation
 *
 * Emulates multi-diameter CNTFET ternary logic gates with chirality-
 * dependent threshold voltage (V_TH), drift modelling, and endurance
 * tracking.  Based on IEDM 2025/2026 CNTFET research:
 *
 *   - Multi-diameter nanotubes: d=1.0nm (LVT), 1.2nm (MVT), 1.4nm (HVT)
 *   - Chirality (m,n) vector determines bandgap → V_TH
 *   - V_TH model: V_TH = 0.2 + (diameter_nm − 1.0) × 0.5  (in volts)
 *   - 48nm pitch, <0.1 V drift, >10^12 cycle endurance (IEDM 2026)
 *   - Huawei 3-level thresholds: LVT 0.2–0.3V, MVT 0.4V, HVT 0.6–0.7V
 *
 * Integration targets:
 *   - trit_stabilize: CNTFET drift parameter feeds PVT sweep
 *   - trit_ecs_gauge: CNTFET endurance replaces DLFET calibration
 *   - trit_hesitation: CNTFET drift → hesitation uncertainty source
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_TRIT_CNTFET_EMU_H
#define SET6_TRIT_CNTFET_EMU_H

#include "set6/trit.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ======================================================== */

#define CNTFET_MAX_DEVICES       64   /**< Max emulated CNTFET devices     */
#define CNTFET_FP_SCALE        1000   /**< Fixed-point ×1000               */
#define CNTFET_DRIFT_MAX_MV     100   /**< Max tolerable drift (mV)        */
#define CNTFET_ENDURANCE_LOG10   12   /**< Target endurance: 10^12 cycles  */
#define CNTFET_PITCH_NM          48   /**< IEDM 2026 pitch (nm)            */

/* Diameter classes (×1000 nm) */
#define CNTFET_DIAM_LVT        1000   /**< 1.0 nm — low V_TH              */
#define CNTFET_DIAM_MVT        1200   /**< 1.2 nm — mid V_TH              */
#define CNTFET_DIAM_HVT        1400   /**< 1.4 nm — high V_TH             */

/* V_TH targets (mV): V_TH = 200 + (d - 1.0) × 500 */
#define CNTFET_VTH_LVT_MV      200   /**< LVT ≈ 0.20 V                   */
#define CNTFET_VTH_MVT_MV      300   /**< MVT ≈ 0.30 V                   */
#define CNTFET_VTH_HVT_MV      400   /**< HVT ≈ 0.40 V                   */

/* Huawei 3-level mapping (mV) */
#define CNTFET_HUAWEI_LVT_MV   250   /**< Huawei LVT: 0.2–0.3 V centre   */
#define CNTFET_HUAWEI_MVT_MV   400   /**< Huawei MVT: 0.4 V              */
#define CNTFET_HUAWEI_HVT_MV   650   /**< Huawei HVT: 0.6–0.7 V centre   */

/* ==== Structures ======================================================= */

/**
 * @brief CNTFET device configuration.
 */
typedef struct {
    int  diameter_nm_x1000;   /**< Nanotube diameter (×1000 nm)         */
    int  chirality_m;         /**< Chirality vector m component         */
    int  chirality_n;         /**< Chirality vector n component         */
    int  drift_mv;            /**< Current V_TH drift (mV)             */
    int  vth_mv;              /**< Computed threshold voltage (mV)      */
    int  cycle_count;         /**< Switching cycles executed            */
    int  endurance_log10;     /**< Target endurance exponent            */
    int  active;              /**< Device is active                     */
    int  faulted;             /**< Device is faulted (drift exceeded)   */
} trit_cntfet_config_t;

/**
 * @brief CNTFET emulator state.
 */
typedef struct {
    int                    initialized;
    trit_cntfet_config_t   devices[CNTFET_MAX_DEVICES];
    int                    device_count;

    /* Global statistics */
    int                    total_cycles;
    int                    total_drifted;     /**< Devices exceeding drift max */
    int                    total_faulted;
    int                    max_drift_mv;      /**< Worst observed drift        */
    int                    avg_vth_mv;        /**< Average V_TH across devices */
} trit_cntfet_state_t;

/* ==== API ============================================================== */

/**
 * @brief Initialise CNTFET emulator.
 * @param st  State to init.
 * @return 0 on success, -1 on NULL.
 */
int cntfet_init(trit_cntfet_state_t *st);

/**
 * @brief Add a CNTFET device with given diameter and chirality.
 * @param st           State.
 * @param diam_x1000   Diameter in nm ×1000 (e.g. 1200 = 1.2 nm).
 * @param chirality_m  m component of (m,n) chiral vector.
 * @param chirality_n  n component of (m,n) chiral vector.
 * @return Device index (>=0) or -1 on error.
 */
int cntfet_add_device(trit_cntfet_state_t *st, int diam_x1000,
                      int chirality_m, int chirality_n);

/**
 * @brief Compute V_TH for a device from its diameter.
 *
 * V_TH(mV) = 200 + (diameter_nm − 1.0) × 500
 *
 * @param diam_x1000  Diameter in nm ×1000.
 * @return V_TH in mV.
 */
int cntfet_compute_vth(int diam_x1000);

/**
 * @brief CNTFET TNAND gate emulation.
 *
 * Balanced ternary NAND using CNTFET thresholds:
 *   TNAND(a, b) = −min(a, b)   (De Morgan in balanced ternary)
 *
 * @param a  First trit input.
 * @param b  Second trit input.
 * @return TNAND result trit.
 */
trit cntfet_tnand(trit a, trit b);

/**
 * @brief CNTFET TNOR gate emulation.
 *
 *   TNOR(a, b) = −max(a, b)
 *
 * @param a  First trit input.
 * @param b  Second trit input.
 * @return TNOR result trit.
 */
trit cntfet_tnor(trit a, trit b);

/**
 * @brief Simulate drift for a device after N switching cycles.
 *
 * Models V_TH drift as: drift_mv += random_walk component.
 * Drift accumulates monotonically (wear) with sub-linear growth.
 *
 * @param st       State.
 * @param device   Device index.
 * @param cycles   Number of switching cycles to simulate.
 * @param seed     PRNG seed for drift noise.
 * @return Updated drift in mV, or -1 on error.
 */
int cntfet_simulate_drift(trit_cntfet_state_t *st, int device,
                          int cycles, uint32_t seed);

/**
 * @brief Stabilise a device: apply compensating voltage shift.
 *
 * If drift > threshold, applies a feedback correction to reduce
 * measured drift toward zero.
 *
 * @param st            State.
 * @param device        Device index.
 * @param threshold_mv  Drift threshold for correction trigger.
 * @return Residual drift after stabilisation (mV), or -1 on error.
 */
int cntfet_stabilize(trit_cntfet_state_t *st, int device, int threshold_mv);

/**
 * @brief Check endurance for a device.
 *
 * @param st      State.
 * @param device  Device index.
 * @return 1 if within endurance spec, 0 if exceeded, -1 on error.
 */
int cntfet_check_endurance(trit_cntfet_state_t *st, int device);

/**
 * @brief Map a device to Huawei 3-level threshold class.
 *
 * Returns 0 = LVT, 1 = MVT, 2 = HVT based on V_TH.
 *
 * @param vth_mv  Threshold voltage in mV.
 * @return 0/1/2 for LVT/MVT/HVT, or -1 if below minimum.
 */
int cntfet_huawei_class(int vth_mv);

/**
 * @brief Get global statistics summary.
 * @param st  State.
 * @return Average V_TH in mV across active devices, or 0 if none.
 */
int cntfet_get_avg_vth(const trit_cntfet_state_t *st);

#ifdef __cplusplus
}
#endif

#endif /* SET6_TRIT_CNTFET_EMU_H */
