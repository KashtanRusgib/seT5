/*
 * samsung_us11170290b2_zid.v
 *
 * Verilog simulation model of the Zero Input Detection (ZID) circuit
 * and associated counter-based summation circuit (CSC) from Samsung
 * patent US11170290B2, FIG 22.
 *
 * Architecture:
 *
 *   Word-line pair (WL1, WL2) per unit synapse
 *       |            |
 *   [NOR gate 2203] — one per synapse position
 *       |
 *       v
 *   Combinational Logic (CL 2205)
 *       |
 *       v
 *   Block Counter Control (BCC) → CSC Counter Circuit
 *
 * ZID Logic:
 *   For each synapse i, the NOR gate computes:
 *     is_zero[i] = NOR(WL1[i] - Vread, WL2[i] - Vread)
 *   Since inputs are digital in this model:
 *     is_zero[i] = ~(v1_is_vpass[i]) & ~(v2_is_vpass[i])
 *   i.e., both word lines at Vread → zero input detected.
 *
 *   The combinational logic ORs all is_zero bits for the current
 *   sensing cycle to generate the BCC signal:
 *     BCC = is_zero[current_synapse]
 *
 * Counter Logic:
 *   The CSC counter increments when:
 *     - The sense amplifier detects conduction (sa_out = 1)
 *     - AND the BCC signal is NOT active (not a zero input)
 *
 *   cnt_enable = sa_out & ~BCC
 *
 * Dot-product correction (computed in separate logic):
 *   z_count += BCC  (count of zero inputs)
 *   P = 2*cnt_out - (S - z_count)
 *
 * Parameters:
 *   VECTOR_SIZE: Maximum number of synapses (word-line pairs)
 *   COUNTER_WIDTH: Bit width of the summation counter
 *
 * SPDX-License-Identifier: GPL-2.0
 */

module samsung_zid_counter #(
    parameter VECTOR_SIZE   = 64,
    parameter COUNTER_WIDTH = 16,
    parameter LOG2_VS       = 7     // ceil(log2(VECTOR_SIZE+1))
) (
    input  wire                     clk,
    input  wire                     rst_n,

    // Control
    input  wire                     start,          // Begin inference cycle
    input  wire                     zid_enable,     // ZID_Enb mode register bit
    input  wire [LOG2_VS-1:0]       vector_size,    // S: actual vector dimension

    // Word-line voltage indicators (1 = Vpass, 0 = Vread)
    input  wire [VECTOR_SIZE-1:0]   wl1_is_vpass,   // V1 per synapse
    input  wire [VECTOR_SIZE-1:0]   wl2_is_vpass,   // V2 per synapse

    // Sense amplifier output (one bit per synapse, sequential)
    input  wire                     sa_out,         // Current synapse conducts
    input  wire                     sa_valid,       // SA output valid strobe

    // Outputs
    output reg  [COUNTER_WIDTH-1:0] cnt_out,        // Conducting synapse count
    output reg  [COUNTER_WIDTH-1:0] z_count,        // Zero input count
    output reg  signed [COUNTER_WIDTH-1:0] dot_product, // Corrected P
    output reg                      done,           // Computation complete
    output wire                     bcc_signal      // Block Counter Control
);

    // ---------------------------------------------------------------
    // Synapse position counter
    // ---------------------------------------------------------------
    reg [LOG2_VS-1:0] syn_idx;

    // ---------------------------------------------------------------
    // ZID NOR gate array (FIG 22, element 2203)
    // ---------------------------------------------------------------
    // For each synapse position i:
    //   is_zero[i] = ~wl1_is_vpass[i] & ~wl2_is_vpass[i]
    // Meaning: both word lines at Vread → zero input
    wire [VECTOR_SIZE-1:0] is_zero;
    genvar gi;
    generate
        for (gi = 0; gi < VECTOR_SIZE; gi = gi + 1) begin : zid_nor
            assign is_zero[gi] = ~wl1_is_vpass[gi] & ~wl2_is_vpass[gi];
        end
    endgenerate

    // ---------------------------------------------------------------
    // Combinational Logic (CL 2205) → BCC signal
    // ---------------------------------------------------------------
    // BCC is asserted when the current synapse has a zero input
    // AND ZID is enabled.
    wire current_is_zero = is_zero[syn_idx];
    assign bcc_signal = zid_enable & current_is_zero;

    // ---------------------------------------------------------------
    // Counter enable: SA detected conduction AND not a zero input
    // ---------------------------------------------------------------
    wire cnt_enable = sa_valid & sa_out & ~bcc_signal;
    wire z_enable   = sa_valid & bcc_signal;

    // ---------------------------------------------------------------
    // Sequential logic: counter accumulation
    // ---------------------------------------------------------------
    reg active;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            cnt_out     <= {COUNTER_WIDTH{1'b0}};
            z_count     <= {COUNTER_WIDTH{1'b0}};
            dot_product <= {COUNTER_WIDTH{1'b0}};
            syn_idx     <= {LOG2_VS{1'b0}};
            done        <= 1'b0;
            active      <= 1'b0;
        end else if (start) begin
            // Reset counters for new inference cycle
            cnt_out     <= {COUNTER_WIDTH{1'b0}};
            z_count     <= {COUNTER_WIDTH{1'b0}};
            dot_product <= {COUNTER_WIDTH{1'b0}};
            syn_idx     <= {LOG2_VS{1'b0}};
            done        <= 1'b0;
            active      <= 1'b1;
        end else if (active && sa_valid) begin
            // Accumulate
            if (cnt_enable)
                cnt_out <= cnt_out + {{(COUNTER_WIDTH-1){1'b0}}, 1'b1};

            if (z_enable)
                z_count <= z_count + {{(COUNTER_WIDTH-1){1'b0}}, 1'b1};

            // Advance to next synapse
            if (syn_idx == vector_size - 1) begin
                // All synapses processed — compute dot-product
                // P = 2*cnt_out_final - (S - z_count_final)
                // Note: cnt_out may have just been incremented
                active <= 1'b0;
                done   <= 1'b1;
            end else begin
                syn_idx <= syn_idx + {{(LOG2_VS-1){1'b0}}, 1'b1};
            end
        end
    end

    // ---------------------------------------------------------------
    // Dot-product correction (combinational from registered values)
    // ---------------------------------------------------------------
    // P = 2*cnt_out - (vector_size - z_count)
    wire [COUNTER_WIDTH-1:0] s_eff;
    assign s_eff = {{(COUNTER_WIDTH-LOG2_VS){1'b0}}, vector_size} - z_count;

    always @(posedge clk) begin
        if (done) begin
            dot_product <= $signed({1'b0, cnt_out, 1'b0}) - $signed({1'b0, s_eff});
        end
    end

endmodule

/*
 * Sense Amplifier Model
 *
 * Models a single-bit sense amplifier connected to one bit line.
 * Detects whether the NAND string conducts based on the unit synapse
 * evaluation: both cells in series must conduct.
 *
 * In multi-bit configuration, multiple instances share output lines
 * to a multi-bit counter.
 */
module samsung_sense_amplifier (
    input  wire clk,
    input  wire rst_n,
    input  wire sense_enable,    // Trigger sensing
    input  wire string_conducts, // Does the NAND string conduct?
    output reg  sa_out,          // Sense result: 1 = conducts
    output reg  sa_valid         // Result valid strobe
);

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            sa_out   <= 1'b0;
            sa_valid <= 1'b0;
        end else if (sense_enable) begin
            sa_out   <= string_conducts;
            sa_valid <= 1'b1;
        end else begin
            sa_valid <= 1'b0;
        end
    end

endmodule

/*
 * Unit Synapse Model
 *
 * Pair of series-connected SLC memory cells.
 * Both must conduct for the string to conduct.
 *
 * Cell conductivity:
 *   At Vread: only erased cells ("1" state) conduct.
 *   At Vpass: all cells conduct.
 */
module samsung_unit_synapse (
    // Weight programming
    input  wire       prog_enable,
    input  wire       weight_pos,    // 1 = weight +1, 0 = weight -1

    // Input voltage pattern (1 = Vpass, 0 = Vread)
    input  wire       v1_is_vpass,   // Voltage on WL1 (FG1)
    input  wire       v2_is_vpass,   // Voltage on WL2 (FG2)

    // Output
    output wire       conducts       // NAND string conducts?
);

    // Stored cell states: 1 = erased, 0 = programmed
    reg fg1_erased;
    reg fg2_erased;

    // Program weight
    always @(posedge prog_enable) begin
        if (weight_pos) begin
            // Weight +1: FG1=erased, FG2=programmed
            fg1_erased <= 1'b1;
            fg2_erased <= 1'b0;
        end else begin
            // Weight -1: FG1=programmed, FG2=erased
            fg1_erased <= 1'b0;
            fg2_erased <= 1'b1;
        end
    end

    // Cell conductivity
    // At Vpass: always conducts (1)
    // At Vread: conducts only if erased (fg_erased == 1)
    wire c1 = v1_is_vpass | fg1_erased;
    wire c2 = v2_is_vpass | fg2_erased;

    // Series connection: both must conduct
    assign conducts = c1 & c2;

endmodule

/*
 * Multi-Block Parallel Inference Engine
 *
 * Implements FIG 27 of the patent: multiple blocks on the same plane
 * are sensed concurrently using multi-bit sense amplifiers.
 * Each block contributes one bit to the multi-bit SA output.
 */
module samsung_multi_block_engine #(
    parameter NUM_BLOCKS    = 4,
    parameter VECTOR_SIZE   = 64,
    parameter COUNTER_WIDTH = 16
) (
    input  wire                         clk,
    input  wire                         rst_n,
    input  wire                         start,
    input  wire                         zid_enable,
    input  wire [$clog2(VECTOR_SIZE):0] vector_size,

    // Per-block word-line patterns
    input  wire [NUM_BLOCKS*VECTOR_SIZE-1:0] wl1_all,
    input  wire [NUM_BLOCKS*VECTOR_SIZE-1:0] wl2_all,

    // Per-block sense amplifier outputs
    input  wire [NUM_BLOCKS-1:0]        sa_outs,
    input  wire                         sa_valid,

    // Per-block dot-product outputs
    output wire [NUM_BLOCKS*COUNTER_WIDTH-1:0] dot_products,
    output wire [NUM_BLOCKS-1:0]               dones
);

    genvar bi;
    generate
        for (bi = 0; bi < NUM_BLOCKS; bi = bi + 1) begin : block_inst
            samsung_zid_counter #(
                .VECTOR_SIZE(VECTOR_SIZE),
                .COUNTER_WIDTH(COUNTER_WIDTH)
            ) zid_cnt (
                .clk(clk),
                .rst_n(rst_n),
                .start(start),
                .zid_enable(zid_enable),
                .vector_size(vector_size[$clog2(VECTOR_SIZE):0]),
                .wl1_is_vpass(wl1_all[bi*VECTOR_SIZE +: VECTOR_SIZE]),
                .wl2_is_vpass(wl2_all[bi*VECTOR_SIZE +: VECTOR_SIZE]),
                .sa_out(sa_outs[bi]),
                .sa_valid(sa_valid),
                .cnt_out(),
                .z_count(),
                .dot_product(dot_products[bi*COUNTER_WIDTH +: COUNTER_WIDTH]),
                .done(dones[bi]),
                .bcc_signal()
            );
        end
    endgenerate

endmodule
