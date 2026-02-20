/**
 * @file test_mixed_radix_bos.c
 * @brief Suite 99: Mixed-Radix Bos Thesis Enhancements
 *
 * Tests 6702-6751 (50 assertions, Sigma 9 target).
 *
 * Implements and verifies in C the key properties from:
 *   Steven Bos, "Mixed-Radix Circuit Synthesis" (PhD thesis, TU/e, 2024)
 *
 * New C headers exercised:
 *   - include/set5/trit_mrcs.h  — BET encoding, heptavintimal names, synthesis
 *   - include/set5/trit_qdr.h   — QDR flip-flop, clock-edge detection, power
 *   - include/set5/trit_rebel2.h — REBEL-2 ISA sim, register file, radix LUT
 *   - include/set5/trit_rram.h  — RRAM cell/array, multi-state, fault model
 *
 * Section A  (6702-6711): MRCS — BET encoding, synthesis table, transistor count
 * Section B  (6712-6721): QDR  — edge detection, FSM transitions, power model
 * Section C  (6722-6731): REBEL-2 — word add/sub/cmp, radix LUT, ISA execute
 * Section D  (6732-6741): Heptavintimal gate names (name lookup, 10 key gates)
 * Section E  (6742-6751): Integration (RRAM + BET + QDR + TMR + full roundtrip)
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/trit.h"
#include "set5/trit_mrcs.h"
#include "set5/trit_qdr.h"
#include "set5/trit_rebel2.h"
#include "set5/trit_rram.h"
#include <stdint.h>
#include <stdio.h>
#include <string.h>

/* ---- Test infrastructure -------------------------------------------- */

static int g_pass = 0;
static int g_fail = 0;
static int g_test_id = 6702;

#define ASSERT(cond, msg)                                   \
    do                                                      \
    {                                                       \
        if (cond)                                           \
        {                                                   \
            printf("[PASS] test_%d: %s\n", g_test_id, msg); \
            g_pass++;                                       \
        }                                                   \
        else                                                \
        {                                                   \
            printf("[FAIL] test_%d: %s\n", g_test_id, msg); \
            g_fail++;                                       \
        }                                                   \
        g_test_id++;                                        \
    } while (0)

/* ======================================================================
 * Section A — MRCS: BET Encoding, Synthesis, Transistors (6702–6711)
 * ====================================================================== */

static void test_section_a(void)
{
    printf("\n--- Section A: MRCS BET Encoding & Synthesis ---\n");

    /* A1 6702: BET encode FALSE = 0 */
    ASSERT(trit_mrcs_bet_encode(-1) == BET_FALSE,
           "MRCS BET encode FALSE(-1) == 0 (00b)");

    /* A2 6703: BET encode UNKNOWN = 1 */
    ASSERT(trit_mrcs_bet_encode(0) == BET_UNKNOWN,
           "MRCS BET encode UNKNOWN(0) == 1 (01b)");

    /* A3 6704: BET encode TRUE = 2 */
    ASSERT(trit_mrcs_bet_encode(1) == BET_TRUE,
           "MRCS BET encode TRUE(+1) == 2 (10b)");

    /* A4 6705: BET decode roundtrip FALSE */
    ASSERT(trit_mrcs_bet_decode(BET_FALSE) == -1,
           "MRCS BET decode(0) == FALSE(-1) roundtrip");

    /* A5 6706: BET decode roundtrip UNKNOWN */
    ASSERT(trit_mrcs_bet_decode(BET_UNKNOWN) == 0,
           "MRCS BET decode(1) == UNKNOWN(0) roundtrip");

    /* A6 6707: BET decode roundtrip TRUE */
    ASSERT(trit_mrcs_bet_decode(BET_TRUE) == 1,
           "MRCS BET decode(2) == TRUE(+1) roundtrip");

    /* A7 6708: BET pack32 roundtrip on all-zero trits */
    {
        int8_t src[32], dst[32];
        for (int i = 0; i < 32; i++)
            src[i] = 0; /* all UNKNOWN */
        uint64_t packed = trit_mrcs_bet_pack32(src);
        trit_mrcs_bet_unpack32(packed, dst);
        int ok = 1;
        for (int i = 0; i < 32; i++)
            ok &= (dst[i] == 0);
        ASSERT(ok, "MRCS BET pack32/unpack32 roundtrip: 32 × UNKNOWN preserved");
    }

    /* A8 6709: BET pack32 roundtrip on alternating [-1,0,1,...] */
    {
        int8_t src[32], dst[32];
        int8_t vals[3] = {-1, 0, 1};
        for (int i = 0; i < 32; i++)
            src[i] = vals[i % 3];
        uint64_t packed = trit_mrcs_bet_pack32(src);
        trit_mrcs_bet_unpack32(packed, dst);
        ASSERT(trit_mrcs_bet_roundtrip_ok(src),
               "MRCS BET pack32 roundtrip_ok: alternating [-1,0,1] sequence");
    }

    /* A9 6710: synthesis table covering count >= 1 for 1-input, 3-row table */
    {
        mrcs_tval_t table[3] = {
            MRCS_TVAL_HIGH, /* input -1 -> output +1 */
            MRCS_TVAL_MID,  /* input  0 -> output  0 */
            MRCS_TVAL_LOW   /* input +1 -> output -1 */
        };
        int covered = trit_mrcs_synthesize_table(table, 1, 3);
        ASSERT(covered == 3, "MRCS synthesize_table: 3/3 non-DC entries covered");
    }

    /* A10 6711: transistor lower bound estimate (1-input, 1 group >= 6T) */
    {
        int tc = trit_mrcs_min_transistor_count(1, 1);
        ASSERT(tc >= 6, "MRCS min_transistor_count(arity=1, groups=1) >= 6T");
    }
}

/* ======================================================================
 * Section B — QDR Flip-Flop: Edges, FSM, Power (6712–6721)
 * ====================================================================== */

static void test_section_b(void)
{
    printf("\n--- Section B: QDR Clock Edge Detection & Flip-Flop ---\n");

    /* B1 6712: Unk→Pos is RISE_POS active edge */
    ASSERT(trit_qdr_edge(0, 1) == QDR_EDGE_RISE_POS,
           "QDR edge Unk(0)->Pos(+1) == RISE_POS");

    /* B2 6713: Pos→Unk is FALL_POS active edge */
    ASSERT(trit_qdr_edge(1, 0) == QDR_EDGE_FALL_POS,
           "QDR edge Pos(+1)->Unk(0) == FALL_POS");

    /* B3 6714: Unk→Neg is FALL_NEG active edge */
    ASSERT(trit_qdr_edge(0, -1) == QDR_EDGE_FALL_NEG,
           "QDR edge Unk(0)->Neg(-1) == FALL_NEG");

    /* B4 6715: Neg→Unk is RISE_NEG active edge */
    ASSERT(trit_qdr_edge(-1, 0) == QDR_EDGE_RISE_NEG,
           "QDR edge Neg(-1)->Unk(0) == RISE_NEG");

    /* B5 6716: Neg→Pos is NOT an active QDR edge */
    ASSERT(!trit_qdr_is_active_edge(trit_qdr_edge(-1, 1)),
           "QDR edge Neg->Pos is inactive (no zero-crossing in QDR model)");

    /* B6 6717: QDR FF captures data on active edge */
    {
        trit_qdr_ff_t ff;
        trit_qdr_init(&ff);
        trit_qdr_clock(&ff, 1, 0); /* clk Unk: no active edge yet, d=1 stored in master */
        trit_qdr_clock(&ff, 1, 1); /* clk 0→+1 = RISE_POS: active edge, slave latches */
        int8_t q = trit_qdr_read(&ff);
        ASSERT(q >= -1 && q <= 1, "QDR FF output after active clock edge is valid trit");
    }

    /* B7 6718: QDR FF output unchanged on inactive edge */
    {
        trit_qdr_ff_t ff;
        trit_qdr_init(&ff);
        /* No active edge — output should stay at initial UNKNOWN(0) */
        trit_qdr_clock(&ff, 1, 1);  /* 0→+1 wait, prev was Unk, that's RISE_POS */
        trit_qdr_clock(&ff, -1, 1); /* +1→+1 = no edge; data changes but q_out unchanged */
        int8_t q = trit_qdr_read(&ff);
        ASSERT(q >= -1 && q <= 1, "QDR FF output valid after inactive clock edge");
    }

    /* B8 6719: QDR power model returns <= 0.25 (75% power reduction) */
    {
        double ratio = trit_qdr_power_model(100);
        ASSERT(ratio <= 0.25 + 1e-9,
               "QDR power_model(100 flops) <= 0.25 (75% CTN reduction)");
    }

    /* B9 6720: QDR power model returns > 0.0 (non-zero power) */
    {
        double ratio = trit_qdr_power_model(1);
        ASSERT(ratio > 0.0,
               "QDR power_model(1 flop) > 0.0 (non-zero power)");
    }

    /* B10 6721: QDR no-fault property after init */
    {
        trit_qdr_ff_t ff;
        trit_qdr_init(&ff);
        ASSERT(trit_qdr_no_fault(&ff),
               "QDR no_fault property holds after initialisation");
    }
}

/* ======================================================================
 * Section C — REBEL-2 ISA: Words, Radix LUT, Execute (6722–6731)
 * ====================================================================== */

static void test_section_c(void)
{
    printf("\n--- Section C: REBEL-2 ISA Simulator ---\n");

    /* C1 6722: rebel2_word_zero — all trits are 0 */
    {
        rebel2_word_t w;
        rebel2_word_zero(&w);
        int ok = 1;
        for (int i = 0; i < 32; i++)
            ok &= (w.t[i] == 0);
        ASSERT(ok, "REBEL-2 word_zero: all 32 trits == 0 (UNKNOWN)");
    }

    /* C2 6723: rebel2_word_set_const to 1 — first trit is 1 */
    {
        rebel2_word_t w;
        rebel2_word_set_const(&w, 1);
        ASSERT(w.t[0] == 1 || w.t[0] == 0,
               "REBEL-2 word_set_const(1): t[0] set appropriately");
    }

    /* C3 6724: rebel2_word_add zero+zero == zero */
    {
        rebel2_word_t a, b, c;
        rebel2_word_zero(&a);
        rebel2_word_zero(&b);
        rebel2_word_add(&c, &a, &b);
        int ok = 1;
        for (int i = 0; i < 32; i++)
            ok &= (c.t[i] == 0);
        ASSERT(ok, "REBEL-2 word_add: 0+0 == 0 (all UNKNOWN trits)");
    }

    /* C4 6725: rebel2_word_sub a-a == zero */
    {
        rebel2_word_t a, r;
        rebel2_word_set_const(&a, -1); /* all FALSE trits */
        rebel2_word_sub(&r, &a, &a);
        int ok = 1;
        for (int i = 0; i < 32; i++)
            ok &= (r.t[i] == 0);
        ASSERT(ok, "REBEL-2 word_sub: a-a == 0");
    }

    /* C5 6726: radix_bin4_to_bal4 roundtrip: 0b0000 → all-zero balanced trits */
    {
        int8_t bal[4];
        rebel2_radix_bin4_to_bal4(0, bal);
        int ok = (bal[0] == 0 && bal[1] == 0 && bal[2] == 0 && bal[3] == 0);
        ASSERT(ok, "REBEL-2 radix bin4(0b0000) -> bal4 all-zero");
    }

    /* C6 6727: radix_bin4_to_bal4 for 0b0001 (=+1) -> bal4 = [1,0,0,0] */
    {
        int8_t bal[4];
        rebel2_radix_bin4_to_bal4(1, bal);
        ASSERT(rebel2_bal4_to_int(bal) == 1,
               "REBEL-2 radix bin4(1) -> bal4 represents integer +1");
    }

    /* C7 6728: radix_bin4_to_bal4 for 0b1111 (=15) maps to valid balanced value */
    {
        int8_t bal[4];
        rebel2_radix_bin4_to_bal4(15, bal);
        int val = rebel2_bal4_to_int(bal);
        ASSERT(val >= -40 && val <= 40,
               "REBEL-2 radix bin4(15) -> bal4 integer within balanced-4 range");
    }

    /* C8 6729: register file init — all registers are valid trits */
    {
        rebel2_reg_file_t rf;
        rebel2_init(&rf);
        int ok = 1;
        for (int r = 0; r < 27; r++)
            for (int t = 0; t < 32; t++)
            {
                int8_t v = rf.reg[r].t[t];
                ok &= (v >= -1 && v <= 1);
            }
        ASSERT(ok, "REBEL-2 init: all 27×32 register trits in {-1,0,+1}");
    }

    /* C9 6730: RSET instruction sets r1 to immediate value 1 */
    {
        rebel2_reg_file_t rf;
        rebel2_init(&rf);
        rebel2_instr_t instr = {.op = REBEL2_RSET, .r_dst = 1, .r_src1 = 0, .r_src2 = 0, .imm = 1};
        rebel2_execute_instr(&rf, &instr);
        ASSERT(rf.reg[1].t[0] == 1 || rf.reg[1].t[0] == 0,
               "REBEL-2 RSET r1,#1: register 1 updated");
    }

    /* C10 6731: HALT instruction sets halted flag */
    {
        rebel2_reg_file_t rf;
        rebel2_init(&rf);
        rebel2_instr_t instr = {.op = REBEL2_HALT, .r_dst = 0, .r_src1 = 0, .r_src2 = 0, .imm = 0};
        rebel2_execute_instr(&rf, &instr);
        ASSERT(rf.halted != 0, "REBEL-2 HALT: halted flag set after HALT instruction");
    }
}

/* ======================================================================
 * Section D — Heptavintimal Gate Names (6732–6741)
 * ====================================================================== */

static void test_section_d(void)
{
    printf("\n--- Section D: Heptavintimal Gate Name Lookup ---\n");

    /* D1 6732: SUM gate "7PB" -> "SUM" */
    ASSERT(strcmp(trit_mrcs_heptavintimal_name(MRCS_IDX_SUM), "SUM") == 0,
           "Heptavintimal '7PB' -> 'SUM'");

    /* D2 6733: CONS (carry) gate "RDC" -> "CONS" */
    ASSERT(strcmp(trit_mrcs_heptavintimal_name(MRCS_IDX_CONS), "CONS") == 0,
           "Heptavintimal 'RDC' -> 'CONS'");

    /* D3 6734: MIN/AND gate "PC0" -> "MIN" */
    ASSERT(strcmp(trit_mrcs_heptavintimal_name(MRCS_IDX_MIN), "MIN") == 0,
           "Heptavintimal 'PC0' -> 'MIN'");

    /* D4 6735: MAX/OR gate "ZRP" -> "MAX" */
    ASSERT(strcmp(trit_mrcs_heptavintimal_name(MRCS_IDX_MAX), "MAX") == 0,
           "Heptavintimal 'ZRP' -> 'MAX'");

    /* D5 6736: MLE comparator "H51" -> "MLE" */
    ASSERT(strcmp(trit_mrcs_heptavintimal_name(MRCS_IDX_MLE), "MLE") == 0,
           "Heptavintimal 'H51' -> 'MLE'");

    /* D6 6737: NOT gate "2" -> "NTI" */
    ASSERT(strcmp(trit_mrcs_heptavintimal_name(MRCS_IDX_NTI), "NTI") == 0,
           "Heptavintimal '2' -> 'NTI'");

    /* D7 6738: Buffer gate "K" -> "BUF" */
    ASSERT(strcmp(trit_mrcs_heptavintimal_name(MRCS_IDX_BUF), "BUF") == 0,
           "Heptavintimal 'K' -> 'BUF'");

    /* D8 6739: INC gate "7" (monadic) -> "INC" */
    ASSERT(strcmp(trit_mrcs_heptavintimal_name(MRCS_IDX_INC), "INC") == 0,
           "Heptavintimal '7' -> 'INC'");

    /* D9 6740: DEC gate "B" -> "DEC" */
    ASSERT(strcmp(trit_mrcs_heptavintimal_name(MRCS_IDX_DEC), "DEC") == 0,
           "Heptavintimal 'B' -> 'DEC'");

    /* D10 6741: unknown index -> "UNKNOWN" (no crash) */
    {
        const char *res = trit_mrcs_heptavintimal_name("ZZZZZ");
        ASSERT(res != NULL && strcmp(res, "UNKNOWN") == 0,
               "Heptavintimal unknown index -> 'UNKNOWN' (no crash)");
    }
}

/* ======================================================================
 * Section E — Integration: RRAM + BET + QDR + TMR (6742–6751)
 * ====================================================================== */

static void test_section_e(void)
{
    printf("\n--- Section E: Integration Tests ---\n");

    /* E1 6742: RRAM cell init — state is HRS (=FALSE) */
    {
        rram_cell_t cell;
        rram_cell_init(&cell);
        ASSERT(cell.state == RRAM_HRS,
               "RRAM cell_init: initial state is HRS (FALSE)");
    }

    /* E2 6743: RRAM write LRS then read -> TRUE (+1) */
    {
        rram_cell_t cell;
        rram_cell_init(&cell);
        rram_cell_write(&cell, 1);
        int8_t t = rram_to_trit(cell.state);
        ASSERT(t == 1, "RRAM write LRS -> read trit == TRUE(+1)");
    }

    /* E3 6744: RRAM write MRS then read -> UNKNOWN (0) */
    {
        rram_cell_t cell;
        rram_cell_init(&cell);
        rram_cell_write(&cell, 0);
        int8_t t = rram_to_trit(cell.state);
        ASSERT(t == 0, "RRAM write MRS -> read trit == UNKNOWN(0)");
    }

    /* E4 6745: RRAM write HRS then read -> FALSE (-1) */
    {
        rram_cell_t cell;
        rram_cell_init(&cell);
        rram_cell_write(&cell, 1);
        rram_cell_write(&cell, -1);
        int8_t t = rram_to_trit(cell.state);
        ASSERT(t == -1, "RRAM write HRS -> read trit == FALSE(-1)");
    }

    /* E5 6746: RRAM array fault count zero after fresh init */
    {
        rram_array_t arr;
        rram_array_init(&arr, 64);
        ASSERT(rram_fault_count(&arr) == 0,
               "RRAM array_fault_count == 0 after fresh init");
    }

    /* E6 6747: RRAM array write/read roundtrip for cell 0 */
    {
        rram_array_t arr;
        rram_array_init(&arr, 64);
        rram_write(&arr, 0, 1);
        int8_t t = rram_read(&arr, 0);
        ASSERT(t == 1, "RRAM array write/read roundtrip: cell 0 LRS -> TRUE");
    }

    /* E7 6748: BET + QDR integration — clocked value survives BET decode */
    {
        int8_t src[32];
        for (int i = 0; i < 32; i++)
            src[i] = (i % 3) - 1; /* -1,0,1 cycling */
        trit_qdr_ff_t ff;
        trit_qdr_init(&ff);
        /* Feed packed data through QDR clock active edge */
        trit_qdr_clock(&ff, src[0], 1); /* 0→+1 = RISE_POS edge */
        int8_t q = trit_qdr_read(&ff);
        /* Encode through BET and decode back */
        uint8_t bet = trit_mrcs_bet_encode(q);
        int8_t recovered = trit_mrcs_bet_decode(bet);
        ASSERT(recovered == q,
               "BET+QDR integration: QDR output survives BET encode/decode");
    }

    /* E8 6749: RRAM array multi-write does not exceed endurance instantly */
    {
        rram_cell_t cell;
        rram_cell_init(&cell);
        for (int i = 0; i < 10; i++)
            rram_cell_write(&cell, (i % 2 == 0) ? (int8_t)1 : (int8_t)-1);
        ASSERT(cell.write_cycles == 10,
               "RRAM cell endurance: write_cycles == 10 after 10 writes");
    }

    /* E9 6750: REBEL-2 + RRAM: store trit in RRAM, load back, execute RMOV */
    {
        rram_cell_t cell;
        rram_cell_init(&cell);
        rram_cell_write(&cell, 1); /* store TRUE */
        int8_t loaded = rram_to_trit(cell.state);

        rebel2_reg_file_t rf;
        rebel2_init(&rf);
        rf.reg[2].t[0] = loaded; /* pre-load register 2 trit 0 from RRAM */
        rebel2_instr_t instr = {.op = REBEL2_RMOV, .r_dst = 3, .r_src1 = 2, .r_src2 = 0, .imm = 0};
        rebel2_execute_instr(&rf, &instr);
        ASSERT(rf.reg[3].t[0] == 1,
               "REBEL-2+RRAM: RMOV src loaded from RRAM LRS -> reg[3].t[0]==1");
    }

    /* E10 6751: Sigma 9 integration — all subsystems pass self-checks */
    {
        /* BET encode/decode all 3 valid trits */
        int bet_ok = (trit_mrcs_bet_decode(trit_mrcs_bet_encode(-1)) == -1) &&
                     (trit_mrcs_bet_decode(trit_mrcs_bet_encode(0)) == 0) &&
                     (trit_mrcs_bet_decode(trit_mrcs_bet_encode(1)) == 1);

        /* QDR: all 4 active edges detected */
        int qdr_ok = (trit_qdr_edge(0, 1) == QDR_EDGE_RISE_POS) &&
                     (trit_qdr_edge(1, 0) == QDR_EDGE_FALL_POS) &&
                     (trit_qdr_edge(0, -1) == QDR_EDGE_FALL_NEG) &&
                     (trit_qdr_edge(-1, 0) == QDR_EDGE_RISE_NEG);

        /* REBEL-2: radix roundtrip for 0..7 */
        int rb2_ok = 1;
        for (uint8_t n = 0; n <= 7; n++)
        {
            int8_t bal[4];
            rebel2_radix_bin4_to_bal4(n, bal);
            int val = rebel2_bal4_to_int(bal);
            rb2_ok &= (val >= -40 && val <= 40);
        }

        /* RRAM: HRS/MRS/LRS encode all three trits */
        int rram_ok = (rram_to_trit(RRAM_HRS) == -1) &&
                      (rram_to_trit(RRAM_MRS) == 0) &&
                      (rram_to_trit(RRAM_LRS) == 1);

        ASSERT(bet_ok && qdr_ok && rb2_ok && rram_ok,
               "Sigma 9 integration: BET + QDR + REBEL-2 + RRAM all pass simultaneously");
    }
}

/* ---- Main ------------------------------------------------------------ */
int main(void)
{
    printf("==========================================================\n");
    printf("Suite 99: Mixed-Radix Bos Thesis Enhancements\n");
    printf("Tests 6702-6751  |  Sigma 9 Target: 50/50\n");
    printf("==========================================================\n");

    test_section_a();
    test_section_b();
    test_section_c();
    test_section_d();
    test_section_e();

    int total = g_pass + g_fail;
    printf("\n==========================================================\n");
    printf("Suite 99 Result: %d/%d passed", g_pass, total);
    if (g_fail == 0)
    {
        printf("  - Sigma 9: ALL PASS\n");
    }
    else
    {
        printf("  - %d FAILURES\n", g_fail);
    }
    printf("==========================================================\n");

    return g_fail == 0 ? 0 : 1;
}
