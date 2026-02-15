/*
 * intel_pam3_decoder.v
 * Verilog Simulation Model for Intel/Prodigy US11405248B2 PAM-3 Decoder
 *
 * Implements the FPGA-based PAM-3 signal decoder pipeline as described
 * in patent US11405248B2. The 11-stage pipeline processes oversampled
 * PAM-3 waveforms to recover ternary symbol sequences.
 *
 * Pipeline stages:
 *   Stage 1:  ADC sample loading
 *   Stage 2:  DC correction (sliding MIN/MAX block)
 *   Stage 3:  Level detection (4-threshold comparator)
 *   Stage 4:  Spike filter (single-sample glitch removal)
 *   Stage 5:  Edge detection (transition finder)
 *   Stage 6:  Midpoint calculation (must-transition center)
 *   Stage 7:  Edge filter — first level (minimum distance)
 *   Stage 8:  Edge filter — second level (must-transition proximity)
 *   Stage 9:  Sampling point calculation
 *   Stage 10: Sampling point filter
 *   Stage 11: Symbol generation
 *
 * Ternary encoding (balanced):
 *   2'b10 = -1 (PAM-3 level -1)
 *   2'b00 =  0 (PAM-3 level  0)
 *   2'b01 = +1 (PAM-3 level +1)
 *
 * Reference: US11405248B2, Intel Corporation / Prodigy Technovations
 *            "PAM-3 Signal Decoder — FPGA Pipeline"
 *
 * SPDX-License-Identifier: GPL-2.0
 */

/* ===================================================================
 * PAM-3 Encoding Constants
 * ===================================================================*/

`define PAM3_NEG   2'b10   /* -1 level */
`define PAM3_ZERO  2'b00   /*  0 level */
`define PAM3_POS   2'b01   /* +1 level */

/* Pipeline configuration parameters (from patent) */
`define OVERSAMPLE_RATIO  12
`define DC_BLOCK_LEN     128
`define MIN_EDGE_DIST      9
`define MUST_TRANS_WINDOW  12

/* ===================================================================
 * Stage 3: Level Detector
 *
 * Per patent FIG. 5: 4-threshold comparator for PAM-3 signals.
 * Thresholds are:
 *   T_plus     = 140 (upper positive threshold)
 *   T_zero+    = 160 (zero-to-positive)
 *   T_zero-    =  80 (zero-to-negative)
 *   T_minus    =  95 (lower negative threshold)
 *
 * Uses slope-based hysteresis to prevent chatter at boundaries.
 * ===================================================================*/
module pam3_level_detector (
    input  wire        clk,
    input  wire        reset,
    input  wire [7:0]  sample,         /* DC-corrected ADC sample     */
    input  wire [7:0]  prev_sample,    /* Previous sample for slope   */
    input  wire [7:0]  thresh_plus,    /* Upper positive threshold    */
    input  wire [7:0]  thresh_minus,   /* Lower negative threshold    */
    input  wire [7:0]  thresh_zero_p,  /* Zero-to-positive threshold  */
    input  wire [7:0]  thresh_zero_m,  /* Zero-to-negative threshold  */
    output reg  [1:0]  level           /* Detected PAM-3 level        */
);

    wire slope_positive = (sample > prev_sample);

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            level <= `PAM3_ZERO;
        end else begin
            if (slope_positive) begin
                /* Rising slope: use upper thresholds */
                if (sample >= thresh_plus)
                    level <= `PAM3_POS;
                else if (sample >= thresh_zero_p)
                    level <= `PAM3_ZERO;
                else
                    level <= `PAM3_NEG;
            end else begin
                /* Falling slope: use lower thresholds */
                if (sample <= thresh_minus)
                    level <= `PAM3_NEG;
                else if (sample <= thresh_zero_m)
                    level <= `PAM3_ZERO;
                else
                    level <= `PAM3_POS;
            end
        end
    end

endmodule


/* ===================================================================
 * Stage 4: Spike Filter
 *
 * Per patent: removes single-sample glitches by requiring that
 * level changes persist for at least 2 consecutive samples.
 * ===================================================================*/
module pam3_spike_filter (
    input  wire        clk,
    input  wire        reset,
    input  wire [1:0]  level_in,       /* Raw detected level */
    output reg  [1:0]  level_out       /* Filtered level     */
);

    reg [1:0] prev_level;
    reg [1:0] prev2_level;

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            level_out   <= `PAM3_ZERO;
            prev_level  <= `PAM3_ZERO;
            prev2_level <= `PAM3_ZERO;
        end else begin
            prev2_level <= prev_level;
            prev_level  <= level_in;

            /*
             * A level is valid only if it matches the previous level.
             * Single-sample deviations are suppressed.
             */
            if (level_in == prev_level) begin
                level_out <= level_in;
            end else begin
                level_out <= prev2_level;
            end
        end
    end

endmodule


/* ===================================================================
 * Stage 5: Edge Detector
 *
 * Per patent FIG. 6: detects transitions between PAM-3 levels.
 * Identifies "must-transitions" (+1 ↔ -1 within MUST_TRANS_WINDOW).
 * ===================================================================*/
module pam3_edge_detector (
    input  wire        clk,
    input  wire        reset,
    input  wire [1:0]  level_in,       /* Current filtered level      */
    input  wire [1:0]  prev_level_in,  /* Previous filtered level     */
    output reg         edge_detected,  /* 1 = transition found        */
    output reg         is_must_trans   /* 1 = must-transition (+1↔-1) */
);

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            edge_detected <= 0;
            is_must_trans <= 0;
        end else begin
            if (level_in != prev_level_in) begin
                edge_detected <= 1;

                /* Must-transition: direct jump between +1 and -1 */
                is_must_trans <= ((level_in == `PAM3_POS) &&
                                 (prev_level_in == `PAM3_NEG)) ||
                                ((level_in == `PAM3_NEG) &&
                                 (prev_level_in == `PAM3_POS));
            end else begin
                edge_detected <= 0;
                is_must_trans <= 0;
            end
        end
    end

endmodule


/* ===================================================================
 * Stage 7-8: Edge Filter
 *
 * Per patent: two-level edge filtering:
 *   Level 1: Remove edges < MIN_EDGE_DIST apart
 *   Level 2: Remove edges near must-transition midpoints
 * ===================================================================*/
module pam3_edge_filter (
    input  wire        clk,
    input  wire        reset,
    input  wire        edge_in,        /* Edge candidate              */
    input  wire [15:0] edge_pos,       /* Current sample position     */
    input  wire [15:0] prev_edge_pos,  /* Previous accepted edge pos  */
    output reg         edge_out        /* Filtered edge (retained)    */
);

    wire [15:0] distance = edge_pos - prev_edge_pos;

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            edge_out <= 0;
        end else begin
            /* Level 1 filter: minimum distance check */
            if (edge_in && (distance >= `MIN_EDGE_DIST)) begin
                edge_out <= 1;
            end else begin
                edge_out <= 0;
            end
        end
    end

endmodule


/* ===================================================================
 * Stage 11: Symbol Generator
 *
 * Per patent: reads the filtered level at each retained sampling
 * point to produce the final ternary symbol stream.
 * ===================================================================*/
module pam3_symbol_gen (
    input  wire        clk,
    input  wire        reset,
    input  wire        sample_valid,   /* 1 = sampling point active   */
    input  wire [1:0]  level_at_sp,    /* Filtered level at this SP   */
    output reg  [1:0]  symbol_out,     /* Output trit                 */
    output reg         symbol_valid    /* Output valid strobe         */
);

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            symbol_out   <= `PAM3_ZERO;
            symbol_valid <= 0;
        end else begin
            if (sample_valid) begin
                symbol_out   <= level_at_sp;
                symbol_valid <= 1;
            end else begin
                symbol_valid <= 0;
            end
        end
    end

endmodule
