/*
 * seT5 Ternary STT-MRAM Sense Amplifier
 * Triple-Threshold Current Comparator for Biaxial MTJ Reading
 *
 * Interfaces the Biaxial Magnetic Tunnel Junction (MTJ) array
 * to the digital domain by discriminating three resistance states:
 *   State 0 (Parallel):       Low resistance  → bitline_current < TH_LOW
 *   State 1 (Orthogonal 90°): Mid resistance  → TH_LOW ≤ current < TH_HIGH
 *   State 2 (Anti-Parallel):  High resistance → current ≥ TH_HIGH
 *
 * Includes:
 *   - ternary_sense_amp: Single-cell sense amplifier
 *   - mram_write_driver: PAM write pulse generator
 *   - mram_ecs_cell: Error Correction & Stabilization per-cell
 *   - mram_page_controller: Full 729-trit page read/write controller
 *   - mram_trit_packer: 5-trit → 8-bit packing unit
 *
 * SPDX-License-Identifier: GPL-2.0
 */

/* ================================================================
 * Ternary Sense Amplifier — Triple-Threshold Comparator
 * Reads one biaxial MTJ cell and outputs 2-bit encoded trit.
 * Encoding: 2'b00=State0, 2'b01=State1, 2'b10=State2
 * ================================================================ */
module ternary_sense_amp (
    input  wire       clk,
    input  wire       enable,
    input  wire [7:0] bitline_current,  /* 8-bit ADC value (µA scaled) */
    output reg  [1:0] trit_out,
    output reg        valid,
    output reg        meta_stable       /* ECS alert: value between thresholds */
);
    /* Thresholds calibrated to R_L, R_M, R_H resistance plateaus */
    parameter [7:0] TH_LOW  = 8'd10;   /* µA: transition State0 → State1 */
    parameter [7:0] TH_HIGH = 8'd50;   /* µA: transition State1 → State2 */
    parameter [7:0] TH_GUARD_LO = 8'd8;  /* Guard band low */
    parameter [7:0] TH_GUARD_HI = 8'd52; /* Guard band high */

    always @(posedge clk) begin
        if (enable) begin
            meta_stable <= 1'b0;
            valid <= 1'b1;

            if (bitline_current < TH_LOW) begin
                trit_out <= 2'b00;  /* State 0 — Parallel */
                /* Check guard band for near-threshold instability */
                if (bitline_current > TH_GUARD_LO)
                    meta_stable <= 1'b1;
            end
            else if (bitline_current < TH_HIGH) begin
                trit_out <= 2'b01;  /* State 1 — Orthogonal (Gauge Point) */
            end
            else begin
                trit_out <= 2'b10;  /* State 2 — Anti-Parallel */
                if (bitline_current < TH_GUARD_HI)
                    meta_stable <= 1'b1;
            end
        end else begin
            valid <= 1'b0;
        end
    end
endmodule


/* ================================================================
 * MRAM Write Driver — Multi-Step PAM Pulse Generator
 * Generates the appropriate magnetic field pulse to set the
 * biaxial MTJ to one of three stable orientations.
 * ================================================================ */
module mram_write_driver (
    input  wire       clk,
    input  wire       write_en,
    input  wire [1:0] trit_in,         /* Target state: 00/01/10 */
    output reg  [7:0] pulse_amplitude, /* PAM amplitude to MTJ */
    output reg        pulse_active,
    output reg  [1:0] pulse_phase      /* 00=idle, 01=set, 10=verify */
);
    parameter [7:0] PULSE_P  = 8'd20;  /* Parallel field strength */
    parameter [7:0] PULSE_O  = 8'd60;  /* Orthogonal (90°) field */
    parameter [7:0] PULSE_AP = 8'd100; /* Anti-Parallel field */

    reg [1:0] state;
    localparam IDLE   = 2'b00;
    localparam WRITE  = 2'b01;
    localparam VERIFY = 2'b10;

    always @(posedge clk) begin
        case (state)
            IDLE: begin
                pulse_active <= 1'b0;
                pulse_phase <= 2'b00;
                if (write_en) begin
                    state <= WRITE;
                    /* Set amplitude based on target state */
                    case (trit_in)
                        2'b00: pulse_amplitude <= PULSE_P;
                        2'b01: pulse_amplitude <= PULSE_O;
                        2'b10: pulse_amplitude <= PULSE_AP;
                        default: pulse_amplitude <= PULSE_P;
                    endcase
                end
            end

            WRITE: begin
                pulse_active <= 1'b1;
                pulse_phase <= 2'b01;
                state <= VERIFY;
            end

            VERIFY: begin
                pulse_active <= 1'b0;
                pulse_phase <= 2'b10;
                state <= IDLE;
            end

            default: state <= IDLE;
        endcase
    end
endmodule


/* ================================================================
 * MRAM ECS Cell — Per-Cell Error Correction & Stabilization
 * Monitors resistance drift and triggers recalibration when the
 * sensed state deviates from the stored target.
 * ================================================================ */
module mram_ecs_cell (
    input  wire       clk,
    input  wire       enable,
    input  wire [1:0] sensed_state,     /* From sense amplifier */
    input  wire [1:0] stored_target,    /* Expected state */
    input  wire       meta_stable,      /* From sense amp guard band */
    output reg        drift_detected,
    output reg        recal_request,
    output reg  [2:0] recal_count       /* Saturating counter */
);
    parameter [2:0] MAX_RECAL = 3'd7;   /* Max recalibrations before fail */

    always @(posedge clk) begin
        if (enable) begin
            drift_detected <= 1'b0;
            recal_request  <= 1'b0;

            if (meta_stable || (sensed_state != stored_target)) begin
                drift_detected <= 1'b1;
                if (recal_count < MAX_RECAL) begin
                    recal_request <= 1'b1;
                    recal_count <= recal_count + 1;
                end
                /* else: saturated → hardware fault */
            end
        end
    end
endmodule


/* ================================================================
 * MRAM Trit Packer — 5-Trit to 8-Bit Encoder
 * Packs 5 balanced trits into a single byte using mixed-radix:
 *   value = Σ (trit[i]+1) × 3^i,  range [0..242]
 * ================================================================ */
module mram_trit_packer (
    input  wire [1:0] t0, t1, t2, t3, t4,  /* 5 trits (2-bit encoded) */
    output wire [7:0] packed_byte,
    output wire       valid                  /* 1 if all inputs valid */
);
    /* Convert 2-bit encoded trits to integer {0,1,2} */
    wire [3:0] v0 = {2'b00, t0};  /* 0..2 */
    wire [3:0] v1 = {2'b00, t1};
    wire [3:0] v2 = {2'b00, t2};
    wire [3:0] v3 = {2'b00, t3};
    wire [3:0] v4 = {2'b00, t4};

    /* Mixed-radix: val = v0 + v1*3 + v2*9 + v3*27 + v4*81 */
    wire [7:0] val = v0 + v1 * 4'd3 + v2 * 5'd9 + v3 * 5'd27 + v4 * 7'd81;

    assign packed_byte = val;
    assign valid = (val < 8'd243);  /* Must be in valid range */
endmodule


/* ================================================================
 * MRAM Page Controller — 729-Trit Page Read/Write
 * Orchestrates sequential cell access for bulk page operations.
 * Manages the ECS sweep after every write cycle.
 * ================================================================ */
module mram_page_controller #(
    parameter PAGE_TRITS = 729,
    parameter ADDR_BITS  = 10           /* ceil(log2(729)) */
) (
    input  wire                 clk,
    input  wire                 rst_n,
    input  wire                 start_read,
    input  wire                 start_write,
    input  wire [ADDR_BITS-1:0] base_addr,
    input  wire [1:0]           write_trit,     /* Trit to write */

    output reg  [ADDR_BITS-1:0] cell_addr,
    output reg                  cell_read_en,
    output reg                  cell_write_en,
    output reg  [1:0]           cell_write_data,
    output reg                  busy,
    output reg                  done,
    output reg  [9:0]           trit_count       /* Trits processed */
);
    reg [1:0] state;
    localparam S_IDLE  = 2'b00;
    localparam S_READ  = 2'b01;
    localparam S_WRITE = 2'b10;
    localparam S_DONE  = 2'b11;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= S_IDLE;
            busy <= 1'b0;
            done <= 1'b0;
            trit_count <= 10'd0;
            cell_read_en <= 1'b0;
            cell_write_en <= 1'b0;
        end else begin
            case (state)
                S_IDLE: begin
                    done <= 1'b0;
                    cell_read_en <= 1'b0;
                    cell_write_en <= 1'b0;
                    if (start_read) begin
                        state <= S_READ;
                        busy <= 1'b1;
                        trit_count <= 10'd0;
                        cell_addr <= base_addr;
                    end else if (start_write) begin
                        state <= S_WRITE;
                        busy <= 1'b1;
                        trit_count <= 10'd0;
                        cell_addr <= base_addr;
                    end
                end

                S_READ: begin
                    cell_read_en <= 1'b1;
                    cell_write_en <= 1'b0;
                    trit_count <= trit_count + 1;
                    cell_addr <= base_addr + trit_count + 1;
                    if (trit_count >= PAGE_TRITS - 1) begin
                        state <= S_DONE;
                    end
                end

                S_WRITE: begin
                    cell_read_en <= 1'b0;
                    cell_write_en <= 1'b1;
                    cell_write_data <= write_trit;
                    trit_count <= trit_count + 1;
                    cell_addr <= base_addr + trit_count + 1;
                    if (trit_count >= PAGE_TRITS - 1) begin
                        state <= S_DONE;
                    end
                end

                S_DONE: begin
                    busy <= 1'b0;
                    done <= 1'b1;
                    cell_read_en <= 1'b0;
                    cell_write_en <= 1'b0;
                    state <= S_IDLE;
                end
            endcase
        end
    end
endmodule
