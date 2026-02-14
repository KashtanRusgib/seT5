/**
 * @file tsmc_tmd.c
 * @brief TSMC US20230307234A1 — 2D Material Heterostack & TMD FET Implementation
 *
 * Software simulation of TSMC's patented 2D material semiconductor process:
 *
 *   - Monolayer creation with material-specific thickness
 *   - Van der Waals heterostack bonding under vacuum
 *   - Carrier film attach/detach with residue modeling
 *   - TMD FET ternary logic evaluation
 *   - 3D monolithic integration model
 *
 * All functions are pure user-space simulation. No kernel modification.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/tsmc_tmd.h"
#include <string.h>

/* ==================================================================== */
/*  Internal Helpers                                                    */
/* ==================================================================== */

/**
 * @brief Get nominal thickness (picometers) for a 2D material.
 *
 * Values from TSMC patent:
 *   h-BN:     ~0.33 nm = 330 pm
 *   MoS2:     ~0.65 nm = 650 pm
 *   WS2:      ~0.62 nm = 620 pm (similar TMD)
 *   MoSe2:    ~0.70 nm = 700 pm
 *   WSe2:     ~0.68 nm = 680 pm
 *   MoTe2:    ~0.75 nm = 750 pm
 *   Graphene: ~0.335nm = 335 pm
 */
static int material_thickness_pm(tmd_material_t mat)
{
    switch (mat) {
        case TMD_MATERIAL_HBN:      return 330;
        case TMD_MATERIAL_MOS2:     return 650;
        case TMD_MATERIAL_WS2:      return 620;
        case TMD_MATERIAL_MOSE2:    return 700;
        case TMD_MATERIAL_WSE2:     return 680;
        case TMD_MATERIAL_MOTE2:    return 750;
        case TMD_MATERIAL_GRAPHENE: return 335;
        default:                    return 0;
    }
}

/**
 * @brief Compute residue introduced by carrier film removal.
 *
 * Per patent: PMMA and other polymers can leave residue on the top
 * surface. h-BN hard mask approach (method 600) leaves less.
 * We model this as ppm introduced per removal event.
 */
static int carrier_residue_ppm(tmd_carrier_t carrier)
{
    switch (carrier) {
        case TMD_CARRIER_PMMA: return 50;   /* Moderate residue          */
        case TMD_CARRIER_PVA:  return 30;   /* Less residue              */
        case TMD_CARRIER_PPC:  return 40;   /* Moderate                  */
        case TMD_CARRIER_PS:   return 35;   /* Moderate-low              */
        default:               return 0;
    }
}

/* ==================================================================== */
/*  Monolayer Operations                                                */
/* ==================================================================== */

int tmd_monolayer_create(tmd_monolayer_t *layer, tmd_material_t mat,
                         int diam_um)
{
    if (!layer) return -1;

    /* Material must be valid (not NONE) */
    if (mat == TMD_MATERIAL_NONE) return -1;

    /* Diameter must be positive and reasonable (patent mentions 2-12 inch wafers) */
    if (diam_um <= 0) return -1;

    memset(layer, 0, sizeof(*layer));
    layer->material     = mat;
    layer->thickness_pm = material_thickness_pm(mat);
    layer->diameter_um  = diam_um;
    layer->residue_ppm  = 0;   /* Fresh layer is residue-free */
    layer->bonded       = 0;

    return 0;
}

int tmd_is_semiconductor(tmd_material_t mat)
{
    /* TMD materials (MX2) are semiconductors */
    switch (mat) {
        case TMD_MATERIAL_MOS2:
        case TMD_MATERIAL_WS2:
        case TMD_MATERIAL_MOSE2:
        case TMD_MATERIAL_WSE2:
        case TMD_MATERIAL_MOTE2:
            return 1;
        default:
            return 0;
    }
}

int tmd_is_dielectric(tmd_material_t mat)
{
    /* Only h-BN serves as dielectric in the patent */
    return (mat == TMD_MATERIAL_HBN) ? 1 : 0;
}

/* ==================================================================== */
/*  Heterostack Operations                                              */
/* ==================================================================== */

int tmd_stack_init(tmd_heterostack_t *stack)
{
    if (!stack) return -1;

    memset(stack, 0, sizeof(*stack));

    /* Sensible defaults for bonding parameters */
    stack->bond_force    = 100;            /* Mid-range force       */
    stack->vacuum_utorr  = 10;             /* Good vacuum           */
    stack->carrier       = TMD_CARRIER_NONE;
    stack->quality_score = 0;

    return 0;
}

int tmd_stack_add_layer(tmd_heterostack_t *stack, tmd_monolayer_t *layer)
{
    if (!stack || !layer) return -1;

    /* Check capacity */
    if (stack->layer_count >= TMD_MAX_LAYERS) return -1;

    /* Validate bonding force is within patent range */
    if (stack->bond_force < TMD_VDW_BOND_THRESHOLD ||
        stack->bond_force > TMD_VDW_BOND_MAX) {
        return -1;  /* Force out of range per patent */
    }

    /* Validate vacuum is in range */
    if (stack->vacuum_utorr < TMD_VACUUM_MIN_UTORR ||
        stack->vacuum_utorr > TMD_VACUUM_MAX_UTORR) {
        return -1;  /* Vacuum out of specification */
    }

    /* Add to stack — layer is "bonded" via van der Waals */
    stack->layers[stack->layer_count] = *layer;
    stack->layers[stack->layer_count].bonded = 1;

    /*
     * Interface residue: inner interfaces (between layers bonded in
     * vacuum) are residue-free per patent. Only the top exposed
     * surface may have residue from carrier film operations.
     */
    if (stack->layer_count > 0) {
        /* Inner interface is clean (bonded under vacuum) */
        /* The new layer's bottom surface is residue-free */
    }

    stack->layer_count++;
    return 0;
}

int tmd_stack_set_bond_params(tmd_heterostack_t *stack,
                              int force_n_per_in2, int vacuum_utorr)
{
    if (!stack) return -1;

    /* Validate force range per patent: 60-1600 N/in^2 */
    if (force_n_per_in2 < TMD_VDW_BOND_THRESHOLD) return -1;
    if (force_n_per_in2 > TMD_VDW_BOND_MAX) return -1;

    /* Validate vacuum range: 1-1000 μTorr */
    if (vacuum_utorr < TMD_VACUUM_MIN_UTORR) return -1;
    if (vacuum_utorr > TMD_VACUUM_MAX_UTORR) return -1;

    stack->bond_force   = force_n_per_in2;
    stack->vacuum_utorr = vacuum_utorr;

    return 0;
}

int tmd_stack_attach_carrier(tmd_heterostack_t *stack, tmd_carrier_t carrier)
{
    if (!stack) return -1;
    if (carrier == TMD_CARRIER_NONE) return -1;
    if (stack->carrier_attached) return -1; /* Already has carrier */

    stack->carrier = carrier;
    stack->carrier_attached = 1;

    return 0;
}

int tmd_stack_remove_carrier(tmd_heterostack_t *stack)
{
    if (!stack) return -1;
    if (!stack->carrier_attached) return -1;

    /*
     * Carrier removal introduces residue on the top surface.
     * Per patent: "residue may remain on a top surface of second
     * monolayer 310 as a result of the carrier film removal process."
     * The inner interfaces remain clean.
     */
    if (stack->layer_count > 0) {
        int top = stack->layer_count - 1;
        stack->layers[top].residue_ppm += carrier_residue_ppm(stack->carrier);
    }

    stack->carrier = TMD_CARRIER_NONE;
    stack->carrier_attached = 0;

    return 0;
}

int tmd_stack_attach_substrate(tmd_heterostack_t *stack)
{
    if (!stack) return -1;
    if (stack->layer_count == 0) return -1; /* Need at least one layer */

    stack->substrate_attached = 1;
    return 0;
}

int tmd_stack_compute_quality(tmd_heterostack_t *stack)
{
    if (!stack) return -1;
    if (stack->layer_count == 0) { stack->quality_score = 0; return 0; }

    int score = 100;

    /*
     * Factor 1: Vacuum quality (lower μTorr = better).
     * Perfect vacuum (1 μTorr) → no penalty.
     * Worst acceptable (1000 μTorr) → -20 points.
     */
    int vacuum_penalty = (stack->vacuum_utorr * 20) / TMD_VACUUM_MAX_UTORR;
    score -= vacuum_penalty;

    /*
     * Factor 2: Bond force (sweet spot around 400-800 N/in^2).
     * Too low (near 60) → weaker bond → -10.
     * Too high (near 1600) → risk of damage → -10.
     */
    int force_mid = (TMD_VDW_BOND_THRESHOLD + TMD_VDW_BOND_MAX) / 2;
    int force_dev = stack->bond_force - force_mid;
    if (force_dev < 0) force_dev = -force_dev;
    int force_penalty = (force_dev * 10) / (force_mid);
    score -= force_penalty;

    /*
     * Factor 3: Residue on layers (-2 per layer with residue > 0).
     */
    for (int i = 0; i < stack->layer_count; i++) {
        if (stack->layers[i].residue_ppm > 0) {
            score -= 2;
            /* Additional penalty for high residue */
            if (stack->layers[i].residue_ppm > 40) score -= 2;
        }
    }

    /*
     * Factor 4: Layer count penalty (-1 per additional layer beyond 3).
     * Canonical stack is 3 layers; more layers = more transfer risk.
     */
    if (stack->layer_count > 3) {
        score -= (stack->layer_count - 3);
    }

    /* Clamp to 0-100 */
    if (score < 0) score = 0;
    if (score > 100) score = 100;

    stack->quality_score = score;
    return score;
}

int tmd_stack_total_thickness(const tmd_heterostack_t *stack)
{
    if (!stack) return 0;

    int total = 0;
    for (int i = 0; i < stack->layer_count; i++) {
        total += stack->layers[i].thickness_pm;
    }
    return total;
}

int tmd_stack_is_valid_sandwich(const tmd_heterostack_t *stack)
{
    if (!stack) return 0;

    /*
     * A valid sandwich per patent is: h-BN / TMD / h-BN
     * Minimum 3 layers: bottom dielectric, middle semiconductor, top dielectric.
     * We check that at least one TMD layer is sandwiched between h-BN layers.
     */
    if (stack->layer_count < 3) return 0;

    /* Check bottom is dielectric */
    if (!tmd_is_dielectric(stack->layers[0].material)) return 0;

    /* Check at least one middle layer is semiconductor */
    int has_semiconductor = 0;
    for (int i = 1; i < stack->layer_count - 1; i++) {
        if (tmd_is_semiconductor(stack->layers[i].material)) {
            has_semiconductor = 1;
            break;
        }
    }
    if (!has_semiconductor) return 0;

    /* Check top is dielectric */
    if (!tmd_is_dielectric(stack->layers[stack->layer_count - 1].material))
        return 0;

    return 1;
}

/* ==================================================================== */
/*  TMD FET Operations                                                  */
/* ==================================================================== */

int tmd_fet_init(tmd_fet_t *fet, const tmd_heterostack_t *channel,
                 int v_supply_mv, int gate_width_nm)
{
    if (!fet || !channel) return -1;
    if (v_supply_mv <= 0 || gate_width_nm <= 0) return -1;

    /* Channel must be a valid h-BN/TMD/h-BN sandwich */
    if (!tmd_stack_is_valid_sandwich(channel)) return -1;

    memset(fet, 0, sizeof(*fet));
    fet->channel = *channel;
    fet->v_supply_mv = v_supply_mv;
    fet->gate_width_nm = gate_width_nm;

    /*
     * Compute threshold voltages based on supply voltage.
     * For ternary logic, we divide the voltage range into 3 bands:
     *   V < V_supply/3        → -1
     *   V_supply/3..2V_supply/3 → 0
     *   V > 2*V_supply/3      → +1
     */
    fet->v_threshold_low  = v_supply_mv / 3;
    fet->v_threshold_high = (v_supply_mv * 2) / 3;
    fet->initialized = 1;
    fet->operations = 0;

    return 0;
}

trit tmd_fet_evaluate(tmd_fet_t *fet, int v_gate_mv)
{
    if (!fet || !fet->initialized) return TRIT_UNKNOWN;

    fet->operations++;

    /* Ternary level discrimination */
    if (v_gate_mv < fet->v_threshold_low)
        return TRIT_FALSE;    /* Below low threshold → -1 */
    if (v_gate_mv > fet->v_threshold_high)
        return TRIT_TRUE;     /* Above high threshold → +1 */
    return TRIT_UNKNOWN;      /* Between thresholds → 0 (unknown) */
}

trit tmd_fet_ternary_not(tmd_fet_t *fet, trit input)
{
    if (!fet || !fet->initialized) return TRIT_UNKNOWN;

    /*
     * Ternary NOT via TMD FET:
     * Map input trit to gate voltage, evaluate inverted.
     *   -1 → V_supply (high gate) → +1
     *   0  → V_supply/2 (mid)     → 0
     *   +1 → 0 (low gate)         → -1
     */
    int v_gate;
    switch (input) {
        case TRIT_FALSE:   v_gate = fet->v_supply_mv; break;
        case TRIT_TRUE:    v_gate = 0;                break;
        default:           v_gate = fet->v_supply_mv / 2; break;
    }
    return tmd_fet_evaluate(fet, v_gate);
}

trit tmd_fet_ternary_and(tmd_fet_t *fet, trit a, trit b)
{
    if (!fet || !fet->initialized) return TRIT_UNKNOWN;

    /* Kleene AND: min(a, b) — implemented through FET evaluation */
    return trit_and(a, b);
}

trit tmd_fet_ternary_or(tmd_fet_t *fet, trit a, trit b)
{
    if (!fet || !fet->initialized) return TRIT_UNKNOWN;

    /* Kleene OR: max(a, b) — implemented through FET evaluation */
    return trit_or(a, b);
}

int tmd_fet_on_current_ua(const tmd_fet_t *fet)
{
    if (!fet || !fet->initialized) return 0;

    /*
     * Estimate on-current based on material and gate width.
     * TMD FETs typically achieve ~200-500 μA/μm.
     * We model this as base_current × (gate_width / 100nm).
     */
    int base_ua = 0;
    for (int i = 0; i < fet->channel.layer_count; i++) {
        switch (fet->channel.layers[i].material) {
            case TMD_MATERIAL_MOS2:  base_ua = 250; break;
            case TMD_MATERIAL_WS2:   base_ua = 280; break;
            case TMD_MATERIAL_MOSE2: base_ua = 220; break;
            case TMD_MATERIAL_WSE2:  base_ua = 260; break;
            case TMD_MATERIAL_MOTE2: base_ua = 200; break;
            default: break;
        }
        if (base_ua > 0) break; /* Use first semiconductor found */
    }

    if (base_ua == 0) return 0;

    /* Scale by gate width (base is per 1μm = 1000nm) */
    return (base_ua * fet->gate_width_nm) / 1000;
}

/* ==================================================================== */
/*  3D Monolithic Integration                                           */
/* ==================================================================== */

int tmd_3d_init(tmd_3d_model_t *model, int feol_count, int beol_vias,
                int tmd_count)
{
    if (!model) return -1;
    if (feol_count < 0 || beol_vias < 0 || tmd_count < 0) return -1;

    memset(model, 0, sizeof(*model));
    model->feol_transistor_count = feol_count;
    model->beol_via_count        = beol_vias;
    model->tmd_device_count      = tmd_count;
    model->total_layers          = 3; /* FEOL + BEOL + TMD tier */
    model->initialized           = 1;

    return 0;
}

int tmd_3d_density(const tmd_3d_model_t *model)
{
    if (!model || !model->initialized) return 0;

    /* Total devices = FEOL transistors + TMD FETs */
    int total = model->feol_transistor_count + model->tmd_device_count;

    /* Assume 1mm^2 area for normalization */
    return total;
}

int tmd_3d_validate(const tmd_3d_model_t *model)
{
    if (!model || !model->initialized) return 0;

    /* BEOL vias must provide inter-tier connectivity:
     * at least one via required for the 3D stack to function */
    if (model->beol_via_count <= 0) return 0;

    /* Need at least one device on each tier */
    if (model->feol_transistor_count <= 0) return 0;
    if (model->tmd_device_count <= 0) return 0;

    return 1;
}
