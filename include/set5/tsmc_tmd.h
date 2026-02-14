/**
 * @file tsmc_tmd.h
 * @brief TSMC US20230307234A1 — 2D Material Heterostack & TMD FET Interface
 *
 * Software model of the TSMC patent describing semiconductor devices
 * built from two-dimensional (2D) material heterostacks:
 *
 *   - TMD (Transition Metal Dichalcogenide) monolayer simulation:
 *     Materials like MoS2, WS2, MoSe2 with sub-nm thickness.
 *   - h-BN (hexagonal Boron Nitride) dielectric layers.
 *   - Van der Waals heterostack formation:
 *     Stack MX2 + h-BN layers via non-covalent bonding.
 *   - TMD FET channel model:
 *     Simulate transistor with TMD heterostack channel region
 *     for ternary logic levels ({-1, 0, +1}).
 *   - 3D monolithic integration model (FEOL/BEOL stacking).
 *
 * Patent key concepts:
 *   - 2D monolayers held by van der Waals force (residue-free)
 *   - h-BN/TMD/h-BN sandwich for channel isolation
 *   - Carrier film transfer process simulation
 *   - Heterostack quality metric: interface cleanliness
 *
 * All operations are user-space simulation; the seT5 microkernel
 * is NOT modified.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET5_TSMC_TMD_H
#define SET5_TSMC_TMD_H

#include "set5/trit.h"
#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==================================================================== */
/*  Constants                                                           */
/* ==================================================================== */

/** Maximum number of monolayers in a heterostack (patent shows 3+) */
#define TMD_MAX_LAYERS          8

/** Maximum carrier film thickness (nm, polymer like PMMA) */
#define TMD_CARRIER_FILM_MAX_NM 500

/** Van der Waals bond threshold (N/m^2 × 1000, integer) */
#define TMD_VDW_BOND_THRESHOLD  60   /* 60 N/in^2 minimum per patent */
#define TMD_VDW_BOND_MAX        1600 /* 1600 N/in^2 max before damage */

/** Vacuum pressure range (Torr × 1e6, integer for simulation) */
#define TMD_VACUUM_MIN_UTORR    1    /* 1×10^-5 Torr */
#define TMD_VACUUM_MAX_UTORR    1000 /* 1×10^-3 Torr */

/* ==================================================================== */
/*  2D Material Types                                                   */
/* ==================================================================== */

/**
 * @brief Types of 2D materials per TSMC patent.
 *
 * TMD = Transition Metal Dichalcogenide (MX2):
 *   M = Mo, W (transition metal)
 *   X = S, Se, Te (chalcogen)
 * h-BN = hexagonal Boron Nitride (dielectric)
 * Graphene = single-layer carbon (conductor)
 */
typedef enum {
    TMD_MATERIAL_NONE = 0,   /**< Uninitialized                        */
    TMD_MATERIAL_HBN,        /**< Hexagonal Boron Nitride (dielectric)  */
    TMD_MATERIAL_MOS2,       /**< Molybdenum Disulfide (semiconductor)  */
    TMD_MATERIAL_WS2,        /**< Tungsten Disulfide (semiconductor)    */
    TMD_MATERIAL_MOSE2,      /**< Molybdenum Diselenide                 */
    TMD_MATERIAL_WSE2,       /**< Tungsten Diselenide                   */
    TMD_MATERIAL_MOTE2,      /**< Molybdenum Ditelluride                */
    TMD_MATERIAL_GRAPHENE    /**< Graphene (conductor, electrode use)    */
} tmd_material_t;

/**
 * @brief Carrier film material (polymer for wafer transfer).
 */
typedef enum {
    TMD_CARRIER_NONE = 0,
    TMD_CARRIER_PMMA,        /**< Polymethyl methacrylate               */
    TMD_CARRIER_PVA,         /**< Polyvinyl alcohol                     */
    TMD_CARRIER_PPC,         /**< Polypropylene carbonate               */
    TMD_CARRIER_PS           /**< Polystyrene                           */
} tmd_carrier_t;

/* ==================================================================== */
/*  Monolayer Structure                                                 */
/* ==================================================================== */

/**
 * @brief A single 2D material monolayer.
 *
 * Per patent: thickness ranges from ~0.33nm (h-BN) to ~0.65nm (MoS2).
 * The residue_ppm field models interface cleanliness — 0 = perfect.
 */
typedef struct {
    tmd_material_t  material;        /**< 2D material type              */
    int             thickness_pm;    /**< Thickness in picometers       */
    int             diameter_um;     /**< Wafer diameter in micrometers */
    int             residue_ppm;     /**< Surface residue (ppm, 0=clean)*/
    int             bonded;          /**< 1 if bonded to stack          */
} tmd_monolayer_t;

/* ==================================================================== */
/*  Heterostack                                                         */
/* ==================================================================== */

/**
 * @brief Stack of 2D monolayers bonded by van der Waals force.
 *
 * The canonical stack from the patent is h-BN / TMD / h-BN, forming
 * a sandwich where h-BN acts as dielectric and TMD as the channel.
 */
typedef struct {
    tmd_monolayer_t layers[TMD_MAX_LAYERS]; /**< Layer stack (bottom→top) */
    int             layer_count;      /**< Number of layers in stack      */
    int             bond_force;       /**< Applied bond force (N/in^2)    */
    int             vacuum_utorr;     /**< Vacuum level during bonding    */
    tmd_carrier_t   carrier;          /**< Carrier film material          */
    int             carrier_attached; /**< 1 if carrier film present      */
    int             substrate_attached;/**< 1 if attached to substrate    */
    int             quality_score;    /**< 0-100 composite quality metric */
} tmd_heterostack_t;

/* ==================================================================== */
/*  TMD FET Transistor Model                                            */
/* ==================================================================== */

/**
 * @brief TMD FET using heterostack as channel region.
 *
 * Per patent FIG. 23: the heterostack forms the channel between
 * source/drain regions with a gate electrode on top.
 *
 * For ternary logic, the FET produces three distinct output levels
 * based on gate voltage:
 *   V_gate < V_th_low  → output = -1 (TRIT_FALSE)
 *   V_th_low <= V_gate <= V_th_high → output = 0 (TRIT_UNKNOWN)
 *   V_gate > V_th_high → output = +1 (TRIT_TRUE)
 */
typedef struct {
    tmd_heterostack_t  channel;         /**< Heterostack channel region */
    int                v_threshold_low; /**< Low threshold (mV)         */
    int                v_threshold_high;/**< High threshold (mV)        */
    int                v_supply_mv;     /**< Supply voltage (mV)        */
    int                gate_width_nm;   /**< Gate width in nanometers   */
    int                initialized;     /**< 1 = ready for operation    */
    int                operations;      /**< Operation counter          */
} tmd_fet_t;

/**
 * @brief 3D monolithic integration model (FEOL + BEOL + TMD).
 *
 * Per patent FIG. 23: FEOL has silicon transistors, BEOL has
 * interconnects, TMD layer sits on top as upper-tier devices.
 */
typedef struct {
    int   feol_transistor_count;  /**< Silicon transistors in FEOL      */
    int   beol_via_count;         /**< Interconnect vias in BEOL        */
    int   tmd_device_count;       /**< TMD FETs on top tier             */
    int   total_layers;           /**< Total 3D stack layers            */
    int   initialized;            /**< 1 = model ready                  */
} tmd_3d_model_t;

/* ==================================================================== */
/*  API — Monolayer Operations                                          */
/* ==================================================================== */

/**
 * @brief Create a 2D monolayer with specified material.
 *
 * Sets thickness based on material type (from patent specifications):
 *   h-BN:  330 pm (0.33 nm)
 *   MoS2:  650 pm (0.65 nm)
 *   WS2:   620 pm
 *   MoSe2: 700 pm
 *   WSe2:  680 pm
 *   MoTe2: 750 pm
 *   Graphene: 335 pm
 *
 * @param layer   Pointer to monolayer struct to initialize
 * @param mat     Material type
 * @param diam_um Wafer diameter in micrometers
 * @return 0 on success, -1 on invalid parameters
 */
int tmd_monolayer_create(tmd_monolayer_t *layer, tmd_material_t mat,
                         int diam_um);

/**
 * @brief Check if material is a TMD (semiconductor) type.
 * @return 1 if TMD, 0 if not
 */
int tmd_is_semiconductor(tmd_material_t mat);

/**
 * @brief Check if material is a dielectric type (h-BN).
 * @return 1 if dielectric, 0 if not
 */
int tmd_is_dielectric(tmd_material_t mat);

/* ==================================================================== */
/*  API — Heterostack Operations                                        */
/* ==================================================================== */

/**
 * @brief Initialize an empty heterostack.
 */
int tmd_stack_init(tmd_heterostack_t *stack);

/**
 * @brief Add a monolayer to the top of the heterostack.
 *
 * Simulates van der Waals bonding. The layer is checked for
 * compatibility and vacuum/force parameters.
 *
 * @param stack Stack to add to
 * @param layer Monolayer to add (will be bonded)
 * @return 0 on success, -1 on error (full, bad force, etc.)
 */
int tmd_stack_add_layer(tmd_heterostack_t *stack, tmd_monolayer_t *layer);

/**
 * @brief Set bonding parameters for the heterostack.
 *
 * @param force_n_per_in2  Bond force (60-1600 N/in^2 per patent)
 * @param vacuum_utorr     Vacuum level (1-1000 μTorr per patent)
 * @return 0 on success, -1 if out of range
 */
int tmd_stack_set_bond_params(tmd_heterostack_t *stack,
                              int force_n_per_in2, int vacuum_utorr);

/**
 * @brief Attach a carrier film for wafer transfer.
 */
int tmd_stack_attach_carrier(tmd_heterostack_t *stack, tmd_carrier_t carrier);

/**
 * @brief Remove carrier film after transfer.
 *
 * May introduce residue on the top layer depending on carrier type.
 */
int tmd_stack_remove_carrier(tmd_heterostack_t *stack);

/**
 * @brief Attach heterostack to a substrate.
 */
int tmd_stack_attach_substrate(tmd_heterostack_t *stack);

/**
 * @brief Compute quality score (0-100) based on bonding parameters.
 *
 * Quality factors:
 *   - Vacuum level (lower = better)
 *   - Bond force (within range = better)
 *   - Residue levels on interfaces
 *   - Layer count (more layers = slightly lower quality)
 */
int tmd_stack_compute_quality(tmd_heterostack_t *stack);

/**
 * @brief Get total stack thickness in picometers.
 */
int tmd_stack_total_thickness(const tmd_heterostack_t *stack);

/**
 * @brief Validate that the stack forms a valid h-BN/TMD/h-BN sandwich.
 * @return 1 if valid sandwich, 0 if not
 */
int tmd_stack_is_valid_sandwich(const tmd_heterostack_t *stack);

/* ==================================================================== */
/*  API — TMD FET Operations                                            */
/* ==================================================================== */

/**
 * @brief Initialize a TMD FET with the given heterostack channel.
 *
 * The heterostack must be a valid h-BN/TMD/h-BN sandwich.
 * Threshold voltages are computed from the TMD material properties.
 */
int tmd_fet_init(tmd_fet_t *fet, const tmd_heterostack_t *channel,
                 int v_supply_mv, int gate_width_nm);

/**
 * @brief Evaluate ternary output of TMD FET for a given gate voltage.
 *
 * Returns the trit value: -1 if Vg < Vth_low, +1 if Vg > Vth_high,
 * 0 otherwise (intermediate/unknown state).
 */
trit tmd_fet_evaluate(tmd_fet_t *fet, int v_gate_mv);

/**
 * @brief Evaluate a balanced ternary inverter (NOT gate) using TMD FET.
 *
 * Maps input trit to gate voltage, evaluates, and returns inverted trit.
 */
trit tmd_fet_ternary_not(tmd_fet_t *fet, trit input);

/**
 * @brief Evaluate ternary AND using complementary TMD FETs.
 */
trit tmd_fet_ternary_and(tmd_fet_t *fet, trit a, trit b);

/**
 * @brief Evaluate ternary OR using complementary TMD FETs.
 */
trit tmd_fet_ternary_or(tmd_fet_t *fet, trit a, trit b);

/**
 * @brief Get the on-current estimate for the FET (microamps).
 *
 * Depends on channel material, thickness, and gate width.
 */
int tmd_fet_on_current_ua(const tmd_fet_t *fet);

/* ==================================================================== */
/*  API — 3D Monolithic Integration                                     */
/* ==================================================================== */

/**
 * @brief Initialize a 3D monolithic model.
 */
int tmd_3d_init(tmd_3d_model_t *model, int feol_count, int beol_vias,
                int tmd_count);

/**
 * @brief Compute total transistor density (devices per mm^2).
 */
int tmd_3d_density(const tmd_3d_model_t *model);

/**
 * @brief Validate 3D stack connectivity.
 * @return 1 if valid, 0 if inconsistent counts
 */
int tmd_3d_validate(const tmd_3d_model_t *model);

#ifdef __cplusplus
}
#endif

#endif /* SET5_TSMC_TMD_H */
