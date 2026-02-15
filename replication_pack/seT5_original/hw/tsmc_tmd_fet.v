/*
 * tsmc_tmd_fet.v
 * Verilog Simulation Model for TSMC US20230307234A1 TMD FET
 *
 * Implements the 2D-material (TMD) field-effect transistor channel
 * model as described in patent US20230307234A1:
 *
 *   1. TMD monolayer channel with configurable material
 *   2. h-BN dielectric insulator layers
 *   3. Ternary threshold logic (V/3 and 2V/3 levels)
 *   4. 3D monolithic integration model (FEOL + BEOL + TMD tiers)
 *
 * Material encoding:
 *   3'b000 = h-BN       (insulator, bandgap ~6.0 eV)
 *   3'b001 = MoS2       (semiconductor, ~1.8 eV)
 *   3'b010 = WS2        (semiconductor, ~2.0 eV)
 *   3'b011 = MoSe2      (semiconductor, ~1.5 eV)
 *   3'b100 = WSe2       (semiconductor, ~1.6 eV)
 *   3'b101 = MoTe2      (semiconductor, ~1.0 eV)
 *   3'b110 = Graphene    (semimetal, ~0 eV)
 *
 * Ternary encoding (balanced):
 *   2'b10 = -1 (FALSE)
 *   2'b00 =  0 (UNKNOWN)
 *   2'b01 = +1 (TRUE)
 *
 * Reference: US20230307234A1, TSMC
 *            "2D Material Heterostack — TMD FET Channels"
 *
 * SPDX-License-Identifier: GPL-2.0
 */

/* ===================================================================
 * Ternary Encoding Constants
 * ===================================================================*/

`define TRIT_NEG  2'b10   /* -1, FALSE  */
`define TRIT_ZERO 2'b00   /*  0, UNKNOWN */
`define TRIT_POS  2'b01   /* +1, TRUE   */

/* ===================================================================
 * Material Constants (3-bit encoding)
 * ===================================================================*/

`define MAT_HBN      3'b000
`define MAT_MOS2     3'b001
`define MAT_WS2      3'b010
`define MAT_MOSE2    3'b011
`define MAT_WSE2     3'b100
`define MAT_MOTE2    3'b101
`define MAT_GRAPHENE 3'b110

/* ===================================================================
 * TMD Monolayer Model
 *
 * Represents a single atomic layer of 2D material.
 * Thickness is fixed per material (in picometers).
 *
 * Per patent: TMD layers are stacked via van der Waals bonding
 * without lattice matching requirements.
 * ===================================================================*/
module tmd_monolayer (
    input  wire [2:0]  material,       /* Material type encoding        */
    input  wire [15:0] diameter_um,    /* Diameter in micrometers       */
    output reg  [15:0] thickness_pm,   /* Layer thickness in picometers */
    output reg         is_insulator,   /* 1 if h-BN or graphene         */
    output reg         is_semiconductor /* 1 if MoS2/WS2/MoSe2/WSe2   */
);

    /* Material thickness lookup (from experimental data) */
    always @(*) begin
        case (material)
            `MAT_HBN:      begin thickness_pm = 16'd330; is_insulator = 1; is_semiconductor = 0; end
            `MAT_MOS2:     begin thickness_pm = 16'd650; is_insulator = 0; is_semiconductor = 1; end
            `MAT_WS2:      begin thickness_pm = 16'd620; is_insulator = 0; is_semiconductor = 1; end
            `MAT_MOSE2:    begin thickness_pm = 16'd700; is_insulator = 0; is_semiconductor = 1; end
            `MAT_WSE2:     begin thickness_pm = 16'd680; is_insulator = 0; is_semiconductor = 1; end
            `MAT_MOTE2:    begin thickness_pm = 16'd750; is_insulator = 0; is_semiconductor = 1; end
            `MAT_GRAPHENE: begin thickness_pm = 16'd335; is_insulator = 1; is_semiconductor = 0; end
            default:       begin thickness_pm = 16'd0;   is_insulator = 0; is_semiconductor = 0; end
        endcase
    end

endmodule


/* ===================================================================
 * TMD FET — Ternary Field-Effect Transistor
 *
 * Per patent: TMD channel transistor with dual threshold voltages
 * for ternary logic evaluation:
 *
 *   Vgs < V_supply/3          → output = -1 (FALSE)
 *   V_supply/3 ≤ Vgs < 2V/3  → output =  0 (UNKNOWN)
 *   Vgs ≥ 2V_supply/3        → output = +1 (TRUE)
 *
 * Gate width and channel material affect on-current.
 * ===================================================================*/
module tmd_fet (
    input  wire        clk,
    input  wire        reset,
    input  wire [2:0]  channel_material, /* TMD channel material        */
    input  wire [15:0] v_gate,           /* Gate voltage (mV, unsigned) */
    input  wire [15:0] v_supply,         /* Supply voltage (mV)         */
    input  wire [15:0] gate_width_nm,    /* Gate width in nanometers    */
    output reg  [1:0]  trit_out,         /* Ternary output              */
    output reg  [15:0] on_current_ua     /* Estimated on-current (μA)   */
);

    /* Internal threshold levels */
    wire [15:0] thresh_low;   /* V_supply / 3 */
    wire [15:0] thresh_high;  /* 2 * V_supply / 3 */

    assign thresh_low  = v_supply / 16'd3;
    assign thresh_high = (v_supply * 16'd2) / 16'd3;

    /* Base on-current lookup per material (μA/μm at 1μm width) */
    reg [15:0] base_current;
    always @(*) begin
        case (channel_material)
            `MAT_MOS2:  base_current = 16'd250;
            `MAT_WS2:   base_current = 16'd230;
            `MAT_MOSE2: base_current = 16'd200;
            `MAT_WSE2:  base_current = 16'd210;
            `MAT_MOTE2: base_current = 16'd280;
            default:    base_current = 16'd0;   /* Non-TMD = no channel */
        endcase
    end

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            trit_out     <= `TRIT_ZERO;
            on_current_ua <= 16'd0;
        end else begin
            /* Ternary threshold evaluation */
            if (v_gate < thresh_low) begin
                trit_out <= `TRIT_NEG;          /* Below lower threshold */
            end else if (v_gate < thresh_high) begin
                trit_out <= `TRIT_ZERO;         /* Between thresholds   */
            end else begin
                trit_out <= `TRIT_POS;          /* Above upper threshold */
            end

            /* On-current estimate: base × (width_nm / 1000) */
            on_current_ua <= (base_current * gate_width_nm) / 16'd1000;
        end
    end

endmodule


/* ===================================================================
 * Van der Waals Bonding Validator
 *
 * Per patent: TMD heterostack layers are bonded via van der Waals
 * forces. Valid bonding requires:
 *   - Bond force: 60 – 1600 N/in²
 *   - Vacuum pressure: 1 – 1000 μTorr
 * ===================================================================*/
module tmd_vdw_bond_check (
    input  wire [15:0] bond_force,       /* N/in² */
    input  wire [15:0] vacuum_utorr,     /* μTorr  */
    output wire        bond_valid
);

    /* Valid ranges per patent specification */
    wire force_ok  = (bond_force >= 16'd60) && (bond_force <= 16'd1600);
    wire vacuum_ok = (vacuum_utorr >= 16'd1) && (vacuum_utorr <= 16'd1000);

    assign bond_valid = force_ok & vacuum_ok;

endmodule


/* ===================================================================
 * h-BN / TMD Sandwich Validator
 *
 * Per patent: optimal FET structure uses h-BN / TMD / h-BN sandwich
 * (insulator / semiconductor / insulator).
 *
 * This module checks if a 3-layer stack has valid sandwich topology.
 * ===================================================================*/
module tmd_sandwich_check (
    input  wire [2:0] layer_bot,   /* Bottom layer material */
    input  wire [2:0] layer_mid,   /* Middle layer material */
    input  wire [2:0] layer_top,   /* Top layer material    */
    output wire       valid_sandwich
);

    /* Bottom and top must be h-BN; middle must be TMD semiconductor */
    wire bot_hbn = (layer_bot == `MAT_HBN);
    wire top_hbn = (layer_top == `MAT_HBN);

    wire mid_tmd = (layer_mid == `MAT_MOS2)  |
                   (layer_mid == `MAT_WS2)   |
                   (layer_mid == `MAT_MOSE2) |
                   (layer_mid == `MAT_WSE2)  |
                   (layer_mid == `MAT_MOTE2);

    assign valid_sandwich = bot_hbn & mid_tmd & top_hbn;

endmodule


/* ===================================================================
 * 3D Monolithic Integration Density Calculator
 *
 * Per patent: TMD layers enable 3D stacking without thermal budget
 * constraints. Integration density = (FEOL + BEOL + TMD) / area.
 * ===================================================================*/
module tmd_3d_density (
    input  wire [7:0]  feol_count,     /* FEOL tier count       */
    input  wire [7:0]  beol_count,     /* BEOL tier count       */
    input  wire [7:0]  tmd_count,      /* TMD tier count        */
    input  wire [15:0] die_area_mm2,   /* Die area in mm²       */
    output reg  [31:0] density         /* Devices per mm² × 100 */
);

    /*
     * Each tier contributes:
     *   FEOL: 100 devices/mm² per tier
     *   BEOL:  50 devices/mm² per tier
     *   TMD:  200 devices/mm² per tier (highest due to monolayer)
     */
    wire [31:0] total_devices;
    assign total_devices = (feol_count * 32'd100) +
                           (beol_count * 32'd50)  +
                           (tmd_count  * 32'd200);

    always @(*) begin
        if (die_area_mm2 > 16'd0) begin
            density = (total_devices * 32'd100) / die_area_mm2;
        end else begin
            density = 32'd0;
        end
    end

endmodule
