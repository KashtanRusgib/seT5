/*
 * hardware/ternary_alu.v - Simplified Ternary ALU Module (TASK-017)
 *
 * Compact ALU following Huawei ternary patent pattern.
 * 2-bit encoding for balanced ternary:
 *   2'b00 = Z (zero)
 *   2'b01 = P (+1)
 *   2'b10 = N (-1)
 *   2'b11 = invalid
 *
 * Operations: add, mul, min, max
 * See also: hw/ternary_alu.v for full 9-trit word ALU + processor.
 */

module ternary_alu (
    input  signed [1:0] a, b,  // 00=0, 01=1, 10=-1
    input  [1:0] op,           // 00=add, 01=mul, 10=min, 11=max
    output reg signed [1:0] out,
    output reg signed [1:0] carry
);
    /* Convert 2-bit trit encoding to signed integer */
    function signed [2:0] decode;
        input [1:0] t;
        begin
            case (t)
                2'b00: decode = 0;
                2'b01: decode = 1;
                2'b10: decode = -1;
                default: decode = 0;
            endcase
        end
    endfunction

    /* Convert signed integer to 2-bit trit encoding */
    function [1:0] encode;
        input signed [2:0] v;
        begin
            case (v)
                0:  encode = 2'b00;
                1:  encode = 2'b01;
                -1: encode = 2'b10;
                default: encode = 2'b00;
            endcase
        end
    endfunction

    reg signed [2:0] s;

    always @(*) begin
        carry = 2'b00; // default no carry
        case (op)
            2'b00: begin // ADD with balanced ternary carry
                s = decode(a) + decode(b);
                if (s > 1) begin
                    out = encode(s - 3);
                    carry = 2'b01; // carry = P
                end else if (s < -1) begin
                    out = encode(s + 3);
                    carry = 2'b10; // carry = N
                end else begin
                    out = encode(s);
                end
            end
            2'b01: begin // MUL: P*P=P, P*N=N, N*N=P, Z*x=Z
                out = encode(decode(a) * decode(b));
            end
            2'b10: begin // MIN
                out = (decode(a) < decode(b)) ? a : b;
            end
            2'b11: begin // MAX
                out = (decode(a) > decode(b)) ? a : b;
            end
        endcase
    end
endmodule
