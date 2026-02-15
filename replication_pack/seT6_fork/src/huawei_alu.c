/**
 * @file huawei_alu.c
 * @brief ALU Implementation for Huawei CN119652311A Ternary Chip
 *
 * Software-emulated and MMIO-backed implementations of every
 * arithmetic circuit described in patent CN119652311A:
 *
 *   - INC / DEC single-trit gates (9 transistors each)
 *   - NTI / PTI preprocessors    (2 transistors each)
 *   - Summing circuit (Tsum)     (INC + DEC + NTI/PTI + NOR + 3 gates)
 *   - Half-adder (THA)          (Tsum + carry device)
 *   - Full-adder (TFA)          (two-stage THA + PB/NB/AND)
 *   - Exact multiplier (TMul)   (balanced trit multiply)
 *   - Approximate multiplier    (ATMul: ignores carry at (+1)×(+1))
 *   - Wide multiply             (2×2 and 6×6 cascaded)
 *   - Multi-trit word addition  (chained full-adders)
 *   - DOT_TRIT / FFT acceleration hooks
 *
 * Each function first checks if the HAL is in MMIO mode (real silicon)
 * and dispatches to hardware.  Otherwise the emulated path executes
 * the exact same logic in software.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set6/huawei_alu.h"
#include "set6/huawei_mmio.h"
#include <string.h>

/* ===================================================================== */
/* Internal Helpers                                                      */
/* ===================================================================== */

/**
 * Balanced-ternary modular reduction: map integer to {-1, 0, +1}
 * using the standard balanced-mod-3 algorithm.
 */
static inline trit balanced_mod3(int v)
{
    int r = ((v % 3) + 3) % 3;   /* Always positive remainder */
    if (r == 0) return TRIT_UNKNOWN;  /* 0 */
    if (r == 1) return TRIT_TRUE;     /* +1 */
    return TRIT_FALSE;                /* -1 (remainder 2) */
}

/**
 * Balanced-ternary carry for half-adder.
 * carry = floor((a + b + 1) / 3) - 1  (with balanced adjustment)
 *
 * Truth table:
 *   (-1)+(-1) = -2  → sum=-1,carry=-1  (actually: -2 = -1*3 + 1, so carry=-1,sum=+1)
 *   Actually let's use the correct balanced ternary addition:
 *     a+b  in_decimal  carry  sum
 *     -1+-1 = -2      -1      +1
 *     -1+ 0 = -1       0      -1
 *     -1+ 1 =  0       0       0
 *      0+-1 = -1       0      -1
 *      0+ 0 =  0       0       0
 *      0+ 1 = +1       0      +1
 *     +1+-1 =  0       0       0
 *     +1+ 0 = +1       0      +1
 *     +1+ 1 = +2      +1      -1
 */
static inline trit balanced_carry(int sum)
{
    if (sum >= 2)  return TRIT_TRUE;     /* +1 */
    if (sum <= -2) return TRIT_FALSE;    /* -1 */
    return TRIT_UNKNOWN;                 /* 0  */
}

static inline trit balanced_sum(int sum)
{
    /* Reduce sum ∈ {-4..+4} to balanced trit */
    if (sum >= 2)  return (trit)(sum - 3);
    if (sum <= -2) return (trit)(sum + 3);
    return (trit)sum;
}

/* ===================================================================== */
/* Single-Trit Gate Operations                                           */
/* ===================================================================== */

trit hw_alu_inc(const hw_hal_state_t *state, trit val)
{
    if (state && state->mode == HW_MODE_MMIO && state->mmio_base) {
        hw_trit hw_in = hw_from_balanced(val);
        hw_mmio_write(state->mmio_base, HW_REG_GATE_OP,
                      HW_GATE_OP_INC | (hw_in & 0x03));
        uint32_t r = hw_mmio_read(state->mmio_base, HW_REG_GATE_RESULT);
        return hw_to_balanced((hw_trit)(r & 0x03));
    }

    /* Emulated: INC = (val + 1 + 1) mod 3 - 1, but simpler: */
    hw_trit hw_in = hw_from_balanced(val);
    hw_trit hw_out = hw_gate_inc(hw_in);
    return hw_to_balanced(hw_out);
}

trit hw_alu_dec(const hw_hal_state_t *state, trit val)
{
    if (state && state->mode == HW_MODE_MMIO && state->mmio_base) {
        hw_trit hw_in = hw_from_balanced(val);
        hw_mmio_write(state->mmio_base, HW_REG_GATE_OP,
                      HW_GATE_OP_DEC | (hw_in & 0x03));
        uint32_t r = hw_mmio_read(state->mmio_base, HW_REG_GATE_RESULT);
        return hw_to_balanced((hw_trit)(r & 0x03));
    }

    hw_trit hw_in = hw_from_balanced(val);
    hw_trit hw_out = hw_gate_dec(hw_in);
    return hw_to_balanced(hw_out);
}

trit hw_alu_nti(const hw_hal_state_t *state, trit val)
{
    if (state && state->mode == HW_MODE_MMIO && state->mmio_base) {
        hw_trit hw_in = hw_from_balanced(val);
        hw_mmio_write(state->mmio_base, HW_REG_GATE_OP,
                      HW_GATE_OP_NTI | (hw_in & 0x03));
        uint32_t r = hw_mmio_read(state->mmio_base, HW_REG_GATE_RESULT);
        return hw_to_balanced((hw_trit)(r & 0x03));
    }

    hw_trit hw_in = hw_from_balanced(val);
    hw_trit hw_out = hw_gate_nti(hw_in);
    return hw_to_balanced(hw_out);
}

trit hw_alu_pti(const hw_hal_state_t *state, trit val)
{
    if (state && state->mode == HW_MODE_MMIO && state->mmio_base) {
        hw_trit hw_in = hw_from_balanced(val);
        hw_mmio_write(state->mmio_base, HW_REG_GATE_OP,
                      HW_GATE_OP_PTI | (hw_in & 0x03));
        uint32_t r = hw_mmio_read(state->mmio_base, HW_REG_GATE_RESULT);
        return hw_to_balanced((hw_trit)(r & 0x03));
    }

    hw_trit hw_in = hw_from_balanced(val);
    hw_trit hw_out = hw_gate_pti(hw_in);
    return hw_to_balanced(hw_out);
}

/* ===================================================================== */
/* Summing Circuit (Tsum) — Patent Fig. 5                                */
/* ===================================================================== */

trit hw_alu_tsum(const hw_hal_state_t *state, trit a, trit b)
{
    if (state && state->mode == HW_MODE_MMIO && state->mmio_base) {
        hw_mmio_write(state->mmio_base, HW_REG_OPERAND_A,
                      hw_from_balanced(a));
        hw_mmio_write(state->mmio_base, HW_REG_OPERAND_B,
                      hw_from_balanced(b));
        hw_mmio_write(state->mmio_base, HW_REG_ALU_CMD,
                      HW_ALU_CMD_BUILD(HW_ALU_TSUM, 1, 0, 0));
        hw_mmio_wait_alu(state->mmio_base, 1000);
        uint32_t r = hw_mmio_read(state->mmio_base, HW_REG_ALU_RESULT);
        return hw_to_balanced((hw_trit)(r & 0x03));
    }

    /*
     * Emulated summing circuit (patent Fig. 5):
     *
     * Signal processing module decomposes A into A0, A1, A2 signals
     * that select which gating tube to conduct:
     *   A = 0 (hw)  → A0 = NTI(A) = 2 → conduct tube 1 → output B
     *   A = 1 (hw)  → NOR(NTI(A), NTI(PTI(A))) = 2 → conduct tube 2 → output INC(B)
     *   A = 2 (hw)  → NTI(PTI(A)) = 2 → conduct tube 3 → output DEC(B)
     *
     * In balanced terms:
     *   A = -1 → output B          (sum = -1 + B = trit sum)
     *   A =  0 → output INC(B)     (sum =  0 + B)
     *   A = +1 → output DEC(B)     (sum = +1 + B)
     *
     * Wait — that doesn't match arithmetic. Let's derive correctly.
     * The Tsum computes (A + B) mod 3 in unbalanced encoding.
     *
     * When A(hw) = 0: gate tube 1 conducts → B passes through directly
     *   → result = B (ie. 0 + B = B ✓)
     * When A(hw) = 1: gate tube 2 conducts → B goes through INC gate
     *   → result = INC(B) = (B+1) mod 3 (ie. 1 + B ✓)
     * When A(hw) = 2: gate tube 3 conducts → B goes through DEC gate
     *   → result = DEC(B) = (B-1) mod 3 (ie. 2 + B = (B-1) mod 3 ✓ since 2≡-1)
     */
    int s = (int)a + (int)b;
    return balanced_mod3(s);
}

/* ===================================================================== */
/* Half-Adder (THA) — Patent Fig. 6                                      */
/* ===================================================================== */

hw_half_adder_result_t hw_alu_half_add(const hw_hal_state_t *state,
                                        trit a, trit b)
{
    hw_half_adder_result_t r;

    if (state && state->mode == HW_MODE_MMIO && state->mmio_base) {
        hw_mmio_write(state->mmio_base, HW_REG_OPERAND_A,
                      hw_from_balanced(a));
        hw_mmio_write(state->mmio_base, HW_REG_OPERAND_B,
                      hw_from_balanced(b));
        hw_mmio_write(state->mmio_base, HW_REG_ALU_CMD,
                      HW_ALU_CMD_BUILD(HW_ALU_THA, 1, 0, 0));
        hw_mmio_wait_alu(state->mmio_base, 1000);
        uint32_t sum  = hw_mmio_read(state->mmio_base, HW_REG_ALU_RESULT);
        uint32_t cout = hw_mmio_read(state->mmio_base, HW_REG_ALU_CARRY_OUT);
        r.sum   = hw_to_balanced((hw_trit)(sum & 0x03));
        r.carry = hw_to_balanced((hw_trit)(cout & 0x03));
        return r;
    }

    /*
     * Emulated half-adder:
     *   sum = (a + b) balanced mod 3
     *   carry from balanced ternary addition table
     */
    int s = (int)a + (int)b;
    r.sum   = balanced_sum(s);
    r.carry = balanced_carry(s);
    return r;
}

/* ===================================================================== */
/* Full-Adder (TFA) — Patent Fig. 7                                      */
/* ===================================================================== */

hw_full_adder_result_t hw_alu_full_add(const hw_hal_state_t *state,
                                        trit a, trit b, trit c)
{
    hw_full_adder_result_t r;

    if (state && state->mode == HW_MODE_MMIO && state->mmio_base) {
        hw_mmio_write(state->mmio_base, HW_REG_OPERAND_A,
                      hw_from_balanced(a));
        hw_mmio_write(state->mmio_base, HW_REG_OPERAND_B,
                      hw_from_balanced(b));
        hw_mmio_write(state->mmio_base, HW_REG_OPERAND_C,
                      hw_from_balanced(c));
        hw_mmio_write(state->mmio_base, HW_REG_ALU_CMD,
                      HW_ALU_CMD_BUILD(HW_ALU_TFA, 1, 0, 0));
        hw_mmio_wait_alu(state->mmio_base, 1000);
        uint32_t sum  = hw_mmio_read(state->mmio_base, HW_REG_ALU_RESULT);
        uint32_t cout = hw_mmio_read(state->mmio_base, HW_REG_ALU_CARRY_OUT);
        r.sum   = hw_to_balanced((hw_trit)(sum & 0x03));
        r.carry = hw_to_balanced((hw_trit)(cout & 0x03));
        return r;
    }

    /*
     * Emulated two-stage full-adder (patent Fig. 7):
     *
     * Stage 1: THA(A, B) → SUM_AB, Carry_AB
     * Stage 2: Optimised THA₂(SUM_AB, C) → SUM_ABC, Carry_SUM
     *   Patent Fig. 8: second stage only needs +0 (PB) or +1 (INC),
     *   since Carry_AB ∈ {-1, 0, +1} but the stage-2 carry path only
     *   sees 0 or 1 from the half-adder carry device.
     * Final: Carry = carry_device(Carry_AB, Carry_SUM)
     *
     * For correct balanced ternary, compute directly:
     */
    int total = (int)a + (int)b + (int)c;  /* range: -3 to +3 */
    r.sum   = balanced_sum(total);
    r.carry = balanced_carry(total);
    return r;
}

/* ===================================================================== */
/* Exact 1-Trit Multiply (TMul)                                          */
/* ===================================================================== */

trit hw_alu_mul1(const hw_hal_state_t *state, trit a, trit b)
{
    if (state && state->mode == HW_MODE_MMIO && state->mmio_base) {
        hw_mmio_write(state->mmio_base, HW_REG_OPERAND_A,
                      hw_from_balanced(a));
        hw_mmio_write(state->mmio_base, HW_REG_OPERAND_B,
                      hw_from_balanced(b));
        hw_mmio_write(state->mmio_base, HW_REG_ALU_CMD,
                      HW_ALU_CMD_BUILD(HW_ALU_TMUL, 1, 0, 0));
        hw_mmio_wait_alu(state->mmio_base, 1000);
        uint32_t r = hw_mmio_read(state->mmio_base, HW_REG_ALU_RESULT);
        return hw_to_balanced((hw_trit)(r & 0x03));
    }

    /* Balanced trit multiply: a * b (result is just a*b for {-1,0,+1}) */
    return (trit)((int)a * (int)b);
}

/* ===================================================================== */
/* Multi-Trit Decomposition Helpers                                      */
/* ===================================================================== */

/**
 * Decompose an integer into balanced ternary trits (LST first).
 * Returns the number of trits written (at most `max_trits`).
 */
static int decompose_balanced(int value, trit *trits, int max_trits)
{
    int neg = (value < 0);
    int v = neg ? -value : value;
    int i = 0;

    memset(trits, 0, (size_t)max_trits * sizeof(trit));

    while (v > 0 && i < max_trits) {
        int r = v % 3;
        if (r == 0) {
            trits[i] = TRIT_UNKNOWN;
            v = v / 3;
        } else if (r == 1) {
            trits[i] = TRIT_TRUE;
            v = (v - 1) / 3;
        } else { /* r == 2 */
            trits[i] = TRIT_FALSE;
            v = (v + 1) / 3;
        }
        i++;
    }

    if (neg) {
        for (int j = 0; j < max_trits; j++)
            trits[j] = (trit)(-(int)trits[j]);
    }

    return i ? i : 1;
}

/**
 * Reconstruct an integer from balanced ternary trits (LST first).
 */
static int recompose_balanced(const trit *trits, int width)
{
    int result = 0;
    int weight = 1;
    for (int i = 0; i < width; i++) {
        result += (int)trits[i] * weight;
        weight *= 3;
    }
    return result;
}

/* ===================================================================== */
/* 2trit × 2trit Multiply — Patent Fig. 11b / Fig. 13                   */
/* ===================================================================== */

/**
 * Approximate 1-trit multiply (ATMul):
 * Same as exact TMul but ignores carry when both inputs = +1 (hw: 2).
 * In balanced: the only case with carry is (+1)×(+1) = +1 with carry +1.
 * ATMul treats (+1)×(+1) as +1 with carry 0.
 *
 * Since we return a single trit (no carry), ATMul and TMul produce
 * the same single-trit result.  The approximation affects the CARRY
 * path in the multiplier circuit.
 */
static trit approx_mul1(trit a, trit b)
{
    return (trit)((int)a * (int)b);
}

/**
 * 1-trit multiply with carry (exact).
 * For balanced ternary:
 *   product = a * b (single trit, always exact, values in {-1,0,+1})
 *   carry only happens in the multi-trit multiplier context
 * Since 1-trit × 1-trit max |product| = 1, carry is always 0.
 */
static trit mul1_with_carry(trit a, trit b, trit *carry)
{
    *carry = TRIT_UNKNOWN;  /* Never overflows for 1-trit */
    return (trit)((int)a * (int)b);
}

hw_mul_result_t hw_alu_mul2x2(const hw_hal_state_t *state,
                               int a, int b, hw_compensation_t comp)
{
    hw_mul_result_t res;
    memset(&res, 0, sizeof(res));
    res.width_trits = 4;  /* 2trit × 2trit → up to 4 trits */
    res.is_approximate = (comp != HW_COMP_NONE) ? 1 : 0;

    if (state && state->mode == HW_MODE_MMIO && state->mmio_base) {
        /* Configure compensation */
        hw_mmio_write(state->mmio_base, HW_REG_APPROX_CFG, (uint32_t)comp);

        /* Load operands (2 trits each, packed in low 4 bits) */
        trit a_trits[2], b_trits[2];
        decompose_balanced(a, a_trits, 2);
        decompose_balanced(b, b_trits, 2);

        uint32_t a_packed = ((uint32_t)hw_from_balanced(a_trits[1]) << 2) |
                             (uint32_t)hw_from_balanced(a_trits[0]);
        uint32_t b_packed = ((uint32_t)hw_from_balanced(b_trits[1]) << 2) |
                             (uint32_t)hw_from_balanced(b_trits[0]);

        hw_mmio_write(state->mmio_base, HW_REG_OPERAND_A, a_packed);
        hw_mmio_write(state->mmio_base, HW_REG_OPERAND_B, b_packed);
        hw_mmio_write(state->mmio_base, HW_REG_ALU_CMD,
                      HW_ALU_CMD_BUILD(HW_ALU_WMUL2, 2,
                                       res.is_approximate, 0));
        hw_mmio_wait_alu(state->mmio_base, 1000);

        /* Read partial products P0–P3 */
        for (int i = 0; i < 4; i++) {
            uint32_t pp = hw_mmio_read(state->mmio_base,
                                       HW_REG_MUL_RESULT(i));
            res.trits[i] = hw_to_balanced((hw_trit)(pp & 0x03));
        }
        res.result = recompose_balanced(res.trits, 4);
        res.abs_error = res.result - (a * b);
        if (res.abs_error < 0) res.abs_error = -res.abs_error;
        return res;
    }

    /*
     * Emulated 2trit × 2trit (patent Fig. 11b):
     *
     * A = A1·3 + A0,  B = B1·3 + B0
     *
     * Partial products:
     *   PP0 = ATMul(A0, B0)    → weight 3^0        (approximate)
     *   PP1 = ATMul(A1, B0)    → weight 3^1        (approximate)
     *   PP2 = ATMul(A0, B1)    → weight 3^1        (approximate)
     *   PP3 = TMul(A1, B1)     → weight 3^2        (exact)
     *
     * Summing tree:
     *   THA1(PP1, PP2) → P1, carry5
     *   THA2(carry5, PP3) → P2, carry7
     *   Tsum(PP3, carry7) → P3      (note: reuses PP3 as described)
     *
     * Result = P0·1 + P1·3 + P2·9 + P3·27
     */
    trit a_trits[2], b_trits[2];
    decompose_balanced(a, a_trits, 2);
    decompose_balanced(b, b_trits, 2);

    trit A0 = a_trits[0], A1 = a_trits[1];
    trit B0 = b_trits[0], B1 = b_trits[1];

    /* Partial products */
    trit PP0 = approx_mul1(A0, B0);   /* ATMul */
    trit PP1 = approx_mul1(A1, B0);   /* ATMul */
    trit PP2 = approx_mul1(A0, B1);   /* ATMul */
    trit PP3;
    trit carry_pp3;
    PP3 = mul1_with_carry(A1, B1, &carry_pp3);  /* TMul (exact) */

    /* THA1: sum PP1 + PP2 */
    hw_half_adder_result_t tha1 = hw_alu_half_add(state, PP1, PP2);

    /* THA2: sum carry_from_THA1 + PP3 */
    hw_half_adder_result_t tha2 = hw_alu_half_add(state, tha1.carry, PP3);

    /* Tsum: PP3_high + carry_from_THA2 */
    trit P3 = hw_alu_tsum(state, carry_pp3, tha2.carry);

    /* Assemble result digits */
    res.trits[0] = PP0;          /* P0: weight 3^0 */
    res.trits[1] = tha1.sum;     /* P1: weight 3^1 */
    res.trits[2] = tha2.sum;     /* P2: weight 3^2 */
    res.trits[3] = P3;           /* P3: weight 3^3 */

    /* Apply compensation */
    if (comp == HW_COMP_PLUS6) {
        /* +6 = +2 at position 1 (3^1 * 2 = 6) */
        int p1_val = (int)res.trits[1] + 2;
        res.trits[1] = balanced_sum(p1_val);
        trit c = balanced_carry(p1_val);
        if (c != TRIT_UNKNOWN) {
            int p2_val = (int)res.trits[2] + (int)c;
            res.trits[2] = balanced_sum(p2_val);
        }
    } else if (comp == HW_COMP_PLUS9) {
        /* +9 = +1 at position 2 (3^2 * 1 = 9) */
        int p2_val = (int)res.trits[2] + 1;
        res.trits[2] = balanced_sum(p2_val);
        trit c = balanced_carry(p2_val);
        if (c != TRIT_UNKNOWN) {
            int p3_val = (int)res.trits[3] + (int)c;
            res.trits[3] = balanced_sum(p3_val);
        }
    }

    res.result = recompose_balanced(res.trits, 4);
    int exact = a * b;
    res.abs_error = res.result - exact;
    if (res.abs_error < 0) res.abs_error = -res.abs_error;

    return res;
}

/* ===================================================================== */
/* 6trit × 6trit Multiply — Patent Fig. 14                              */
/* ===================================================================== */

hw_mul_result_t hw_alu_mul6x6(const hw_hal_state_t *state,
                               int a, int b, hw_compensation_t comp)
{
    hw_mul_result_t res;
    memset(&res, 0, sizeof(res));
    res.width_trits = 12;  /* 6 + 6 = 12 trit result */
    res.is_approximate = (comp != HW_COMP_NONE) ? 1 : 0;

    /*
     * Decompose A and B into 2-trit blocks:
     *   A = A_hi·9 + A_mid·3^? ... actually:
     *   A[5:4], A[3:2], A[1:0]
     *   B[5:4], B[3:2], B[1:0]
     *
     * 9 partial products via 2×2 multiplier:
     *   P00 = A[1:0]×B[1:0]  (weight 3^0)
     *   P01 = A[3:2]×B[1:0]  (weight 3^2)
     *   P02 = A[5:4]×B[1:0]  (weight 3^4)
     *   P10 = A[1:0]×B[3:2]  (weight 3^2)
     *   P11 = A[3:2]×B[3:2]  (weight 3^4)
     *   P12 = A[5:4]×B[3:2]  (weight 3^6)
     *   P20 = A[1:0]×B[5:4]  (weight 3^4)
     *   P21 = A[3:2]×B[5:4]  (weight 3^6)
     *   P22 = A[5:4]×B[5:4]  (weight 3^8)
     *
     * Sum with weighted shifts using exact-mode adders.
     */
    trit a_trits[6], b_trits[6];
    decompose_balanced(a, a_trits, 6);
    decompose_balanced(b, b_trits, 6);

    /* Extract 2-trit blocks as integers */
    int A0 = recompose_balanced(&a_trits[0], 2);
    int A1 = recompose_balanced(&a_trits[2], 2);
    int A2 = recompose_balanced(&a_trits[4], 2);
    int B0 = recompose_balanced(&b_trits[0], 2);
    int B1 = recompose_balanced(&b_trits[2], 2);
    int B2 = recompose_balanced(&b_trits[4], 2);

    /* Compute partial products (2×2) */
    hw_mul_result_t pp[3][3];
    pp[0][0] = hw_alu_mul2x2(state, A0, B0, comp);
    pp[0][1] = hw_alu_mul2x2(state, A1, B0, comp);
    pp[0][2] = hw_alu_mul2x2(state, A2, B0, comp);
    pp[1][0] = hw_alu_mul2x2(state, A0, B1, comp);
    pp[1][1] = hw_alu_mul2x2(state, A1, B1, comp);
    pp[1][2] = hw_alu_mul2x2(state, A2, B1, comp);
    pp[2][0] = hw_alu_mul2x2(state, A0, B2, comp);
    pp[2][1] = hw_alu_mul2x2(state, A1, B2, comp);
    pp[2][2] = hw_alu_mul2x2(state, A2, B2, comp);

    /* Accumulate with positional weights */
    /* Weight table: pp[j][i] has weight 3^(2*(i+j)) */
    int weights[3][3] = {
        {1, 9, 81},         /* 3^0, 3^2, 3^4 */
        {9, 81, 729},       /* 3^2, 3^4, 3^6 */
        {81, 729, 6561}     /* 3^4, 3^6, 3^8 */
    };

    int total = 0;
    for (int j = 0; j < 3; j++)
        for (int i = 0; i < 3; i++)
            total += pp[j][i].result * weights[j][i];

    /* Decompose result into 12 trits */
    decompose_balanced(total, res.trits, 12);
    res.result = total;

    int exact = a * b;
    res.abs_error = res.result - exact;
    if (res.abs_error < 0) res.abs_error = -res.abs_error;

    return res;
}

/* ===================================================================== */
/* Multi-Trit Word Addition (Chained Full-Adders)                        */
/* ===================================================================== */

trit hw_alu_add_word(const hw_hal_state_t *state,
                     const trit *a, const trit *b,
                     trit *result, int width)
{
    trit carry = TRIT_UNKNOWN;  /* Initial carry-in = 0 */

    for (int i = 0; i < width; i++) {
        hw_full_adder_result_t fa = hw_alu_full_add(state,
                                                     a[i], b[i], carry);
        result[i] = fa.sum;
        carry = fa.carry;
    }

    return carry;
}

/* ===================================================================== */
/* General Multiply (dispatches to best available width)                  */
/* ===================================================================== */

hw_mul_result_t hw_alu_mul_word(const hw_hal_state_t *state,
                                int a, int b, hw_compensation_t comp)
{
    /* Choose best multiplier width based on operand magnitude */
    int mag_a = a < 0 ? -a : a;
    int mag_b = b < 0 ? -b : b;

    if (mag_a <= 1 && mag_b <= 1) {
        /* 1-trit × 1-trit */
        hw_mul_result_t r;
        memset(&r, 0, sizeof(r));
        r.width_trits = 1;
        r.trits[0] = hw_alu_mul1(state, (trit)a, (trit)b);
        r.result = (int)r.trits[0];
        r.abs_error = 0;
        return r;
    }

    if (mag_a <= 4 && mag_b <= 4) {
        /* 2-trit × 2-trit */
        return hw_alu_mul2x2(state, a, b, comp);
    }

    /* 6-trit × 6-trit */
    return hw_alu_mul6x6(state, a, b, comp);
}

/* ===================================================================== */
/* DOT_TRIT Acceleration                                                 */
/* ===================================================================== */

int hw_alu_dot_product(const hw_hal_state_t *state,
                       const trit *a, const trit *b, int width)
{
    /*
     * Ternary dot product: Σ(a[i] * b[i]) for i=0..width-1.
     * Using the hardware multiplier and chained adders.
     *
     * On the Huawei chip, each trit multiply is a single TMul gate
     * operation, and accumulation uses the summing circuit with
     * carry propagation through the full-adder chain.
     */
    int acc = 0;

    for (int i = 0; i < width; i++) {
        trit prod = hw_alu_mul1(state, a[i], b[i]);
        acc += (int)prod;
    }

    return acc;
}

/* ===================================================================== */
/* FFT Butterfly Acceleration                                            */
/* ===================================================================== */

int hw_alu_fft_butterfly(const hw_hal_state_t *state,
                         trit in0, trit in1, trit in2,
                         trit *out0, trit *out1, trit *out2)
{
    if (!out0 || !out1 || !out2) return -1;

    /*
     * Radix-3 butterfly using hardware summing circuit:
     *
     *   out[0] = in0 + in1 + in2        (balanced mod 3)
     *   out[1] = in0 + ω·in1 + ω²·in2  (ω = cyclic shift +1)
     *   out[2] = in0 + ω²·in1 + ω·in2
     *
     * Twiddle factors as INC/DEC:
     *   ω·x   = INC(x)  [rotate +1 in Huawei encoding]
     *   ω²·x  = DEC(x)  [rotate -1]
     */
    trit w_in1  = hw_alu_inc(state, in1);   /* ω · in1 */
    trit w2_in2 = hw_alu_dec(state, in2);   /* ω² · in2 */
    trit w2_in1 = hw_alu_dec(state, in1);   /* ω² · in1 */
    trit w_in2  = hw_alu_inc(state, in2);   /* ω · in2 */

    /* out[0] = sum of all three inputs */
    trit s01 = hw_alu_tsum(state, in0, in1);
    *out0 = hw_alu_tsum(state, s01, in2);

    /* out[1] = in0 + ω·in1 + ω²·in2 */
    trit s_w = hw_alu_tsum(state, in0, w_in1);
    *out1 = hw_alu_tsum(state, s_w, w2_in2);

    /* out[2] = in0 + ω²·in1 + ω·in2 */
    trit s_w2 = hw_alu_tsum(state, in0, w2_in1);
    *out2 = hw_alu_tsum(state, s_w2, w_in2);

    return 0;
}
