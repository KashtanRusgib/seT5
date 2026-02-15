/**
 * @file trit_art9_pipeline.c
 * @brief seT6 ART-9 RISC Ternary Pipeline Emulator — implementation.
 *
 * Cycle-accurate 5-stage pipeline with 24 balanced ternary instructions,
 * RAW hazard detection, outlier clamping, and energy model.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "trit_art9_pipeline.h"
#include <string.h>

/* ==== Helpers =========================================================== */

int art9_clamp(int val) {
    if (val > ART9_WORD_MAX) return ART9_WORD_MAX;
    if (val < ART9_WORD_MIN) return ART9_WORD_MIN;
    return val;
}

/** Sign function: -1, 0, +1 */
static int art9_sign(int val) {
    if (val > 0) return 1;
    if (val < 0) return -1;
    return 0;
}

/** Balanced ternary shift left: multiply by 3 */
static int art9_shl(int val) { return art9_clamp(val * 3); }

/** Balanced ternary shift right: divide by 3 (round toward zero) */
static int art9_shr(int val) {
    if (val >= 0) return val / 3;
    return -((-val) / 3);
}

/** Absolute value */
static int art9_abs(int val) { return (val < 0) ? -val : val; }

/* ==== Public API ======================================================== */

int art9_init(art9_state_t *st) {
    if (!st) return -1;
    memset(st, 0, sizeof(*st));
    st->initialized = 1;
    return 0;
}

int art9_load_program(art9_state_t *st, const art9_instruction_t *prog,
                      int count) {
    if (!st || !st->initialized || !prog) return -1;
    if (count <= 0 || count > ART9_MAX_PROGRAM) return -1;

    memcpy(st->program, prog, (size_t)count * sizeof(art9_instruction_t));
    st->program_len = count;
    st->pc = 0;
    st->halted = 0;

    /* Clear pipeline stages */
    memset(st->stages, 0, sizeof(st->stages));

    return 0;
}

int art9_execute_alu(art9_state_t *st, const art9_instruction_t *inst) {
    if (!st || !inst) return 0;

    int a = 0, b = 0, result = 0;

    /* Read source registers (bounds-checked) */
    if (inst->rs1 >= 0 && inst->rs1 < ART9_NUM_REGS)
        a = st->regs[inst->rs1];
    if (inst->rs2 >= 0 && inst->rs2 < ART9_NUM_REGS)
        b = st->regs[inst->rs2];

    switch (inst->opcode) {
    case ART9_NOP:    result = 0; break;
    case ART9_TADD:   result = art9_clamp(a + b); break;
    case ART9_TSUB:   result = art9_clamp(a - b); break;
    case ART9_TMUL:   result = art9_clamp(a * b); break;
    case ART9_TNEG:   result = -a; break;
    case ART9_TAND:   result = (a < b) ? a : b; break;  /* Kleene min */
    case ART9_TOR:    result = (a > b) ? a : b; break;  /* Kleene max */
    case ART9_TNOT:   result = -a; break;
    case ART9_TMIN:   result = (a < b) ? a : b; break;
    case ART9_TMAX:   result = (a > b) ? a : b; break;
    case ART9_TSHL:   result = art9_shl(a); break;
    case ART9_TSHR:   result = art9_shr(a); break;
    case ART9_TCMP:   result = art9_sign(a - b); break;
    case ART9_TADDI:  result = art9_clamp(a + inst->imm); break;
    case ART9_TMOVI:  result = art9_clamp(inst->imm); break;
    case ART9_TABS:   result = art9_abs(a); break;
    case ART9_TCLAMP: result = art9_clamp(a); break;

    case ART9_TLOAD:
        if (a >= 0 && a < ART9_MEM_SIZE)
            result = st->memory[a];
        else
            result = 0;
        break;

    case ART9_TSTORE:
        if (a >= 0 && a < ART9_MEM_SIZE)
            st->memory[a] = b;
        result = 0;
        break;

    /* Branches: return comparison result for branch logic */
    case ART9_TBEQ:  result = (a == 0) ? 1 : 0; break;
    case ART9_TBNE:  result = (a != 0) ? 1 : 0; break;
    case ART9_TBGT:  result = (a > 0)  ? 1 : 0; break;
    case ART9_TBLT:  result = (a < 0)  ? 1 : 0; break;

    case ART9_THALT:  st->halted = 1; result = 0; break;
    default:          result = 0; break;
    }

    /* Track outlier clamping */
    if (result != art9_clamp(result)) {
        result = art9_clamp(result);
        st->outlier_clamps++;
    }

    return result;
}

/** Check if instruction writes to a register */
static int art9_writes_reg(const art9_instruction_t *inst) {
    switch (inst->opcode) {
    case ART9_TSTORE: case ART9_THALT: case ART9_NOP:
    case ART9_TBEQ: case ART9_TBNE: case ART9_TBGT: case ART9_TBLT:
        return 0;
    default:
        return 1;
    }
}

/** Check if instruction reads rs1 */
static int art9_reads_rs1(const art9_instruction_t *inst) {
    switch (inst->opcode) {
    case ART9_NOP: case ART9_TMOVI: case ART9_THALT:
        return 0;
    default:
        return 1;
    }
}

/** Check if instruction reads rs2 */
static int art9_reads_rs2(const art9_instruction_t *inst) {
    switch (inst->opcode) {
    case ART9_NOP: case ART9_TMOVI: case ART9_THALT:
    case ART9_TNEG: case ART9_TNOT: case ART9_TSHL: case ART9_TSHR:
    case ART9_TABS: case ART9_TCLAMP: case ART9_TADDI: case ART9_TLOAD:
    case ART9_TBEQ: case ART9_TBNE: case ART9_TBGT: case ART9_TBLT:
        return 0;
    default:
        return 1;
    }
}

/** Check for RAW hazard: does stage[idx] write to a reg that fetch needs? */
static int art9_has_hazard(art9_state_t *st, int fetch_rs, int stage_idx) {
    if (stage_idx < 0 || stage_idx >= ART9_PIPELINE_STAGES) return 0;
    art9_stage_t *s = &st->stages[stage_idx];
    if (!s->valid) return 0;
    if (!art9_writes_reg(&s->inst)) return 0;
    return (s->inst.rd == fetch_rs);
}

/** Is instruction a branch? */
static int art9_is_branch(art9_opcode_t op) {
    return (op == ART9_TBEQ || op == ART9_TBNE ||
            op == ART9_TBGT || op == ART9_TBLT);
}

int art9_cycle(art9_state_t *st) {
    if (!st || !st->initialized) return -1;
    if (st->halted) return 1;

    st->cycles++;

    /* === Writeback (stage 4) === */
    art9_stage_t *wb = &st->stages[4];
    if (wb->valid) {
        if (art9_writes_reg(&wb->inst)) {
            int rd = wb->inst.rd;
            if (rd >= 0 && rd < ART9_NUM_REGS) {
                st->regs[rd] = wb->result;
            }
        }
        st->instructions_retired++;
        st->energy_fj += ART9_ENERGY_PER_INST_FJ;
        wb->valid = 0;
    }

    /* === Advance stages 3→4, 2→3, 1→2 === */
    st->stages[4] = st->stages[3];
    st->stages[3] = st->stages[2];
    st->stages[2] = st->stages[1];

    /* === Execute (stage 2, now contains what was decode) === */
    if (st->stages[2].valid) {
        st->stages[2].result = art9_execute_alu(st, &st->stages[2].inst);

        /* Handle branches */
        if (art9_is_branch(st->stages[2].inst.opcode)) {
            if (st->stages[2].result) {
                /* Branch taken: jump by immediate offset */
                st->pc = st->pc + st->stages[2].inst.imm;
                if (st->pc < 0) st->pc = 0;
                if (st->pc >= st->program_len) st->pc = st->program_len;
                st->branches_taken++;

                /* Flush stages 0 and 1 (speculative work) */
                st->stages[0].valid = 0;
                st->stages[1].valid = 0;
            }
        }
    }

    /* === Fetch + Decode (stage 0 → stage 1) === */
    st->stages[1] = st->stages[0];
    memset(&st->stages[0], 0, sizeof(art9_stage_t));

    if (st->pc < st->program_len && !st->halted) {
        art9_instruction_t *next = &st->program[st->pc];

        /* RAW hazard check: stall if source depends on in-flight write */
        int hazard = 0;
        for (int s = 1; s <= 3; s++) {
            if ((art9_reads_rs1(next) && art9_has_hazard(st, next->rs1, s)) ||
                (art9_reads_rs2(next) && art9_has_hazard(st, next->rs2, s))) {
                hazard = 1;
                break;
            }
        }

        if (hazard) {
            st->stalls++;
            /* Insert bubble: don't advance PC */
        } else {
            st->stages[0].valid = 1;
            st->stages[0].inst = *next;
            st->stages[0].result = 0;
            st->stages[0].stalled = 0;
            st->pc++;
        }
    }

    return st->halted ? 1 : 0;
}

int art9_run(art9_state_t *st, int max_cycles) {
    if (!st || !st->initialized) return -1;
    if (st->program_len <= 0) return -1;

    /* Reset pipeline and stats */
    st->pc = 0;
    st->halted = 0;
    st->cycles = 0;
    st->instructions_retired = 0;
    st->stalls = 0;
    st->branches_taken = 0;
    st->outlier_clamps = 0;
    st->energy_fj = 0;
    memset(st->stages, 0, sizeof(st->stages));

    int c = 0;
    while (c < max_cycles) {
        int rc = art9_cycle(st);
        if (rc == 1) break;  /* halted */
        if (rc == -1) return -1;
        c++;

        /* Also halt if all stages are empty and PC past end */
        if (st->pc >= st->program_len) {
            int any_valid = 0;
            for (int s = 0; s < ART9_PIPELINE_STAGES; s++) {
                if (st->stages[s].valid) { any_valid = 1; break; }
            }
            if (!any_valid) break;
        }
    }

    /* Drain pipeline: flush remaining in-flight instructions to writeback */
    for (int drain = 0; drain < ART9_PIPELINE_STAGES + 1; drain++) {
        /* Writeback */
        art9_stage_t *wb = &st->stages[4];
        if (wb->valid) {
            if (art9_writes_reg(&wb->inst)) {
                int rd = wb->inst.rd;
                if (rd >= 0 && rd < ART9_NUM_REGS)
                    st->regs[rd] = wb->result;
            }
            st->instructions_retired++;
            st->energy_fj += ART9_ENERGY_PER_INST_FJ;
            wb->valid = 0;
        }
        /* Advance stages */
        st->stages[4] = st->stages[3];
        st->stages[3] = st->stages[2];
        st->stages[2] = st->stages[1];
        st->stages[1] = st->stages[0];
        memset(&st->stages[0], 0, sizeof(art9_stage_t));
        /* Execute if valid */
        if (st->stages[2].valid && st->stages[2].inst.opcode != ART9_THALT) {
            st->stages[2].result = art9_execute_alu(st, &st->stages[2].inst);
        }
        st->cycles++;
    }

    return st->cycles;
}

int art9_radix_economy(int n) {
    if (n <= 1) return 1000; /* log ratio = 1.0 for trivial */

    /* Compute log₃(n) / log₂(n) in fixed-point ×1000.
     * log₃(n) / log₂(n) = ln(2) / ln(3) ≈ 0.6309.
     * This is constant and independent of n — it represents the
     * inherent efficiency of ternary vs binary.
     * For n-dependent: log₃(n) = log₂(n) / log₂(3) ≈ log₂(n) / 1.585
     * Radix economy = digits × radix: ternary wins at b*logb(N) for b=3.
     */

    /* Integer log₂ approximation */
    int log2_n = 0;
    int tmp = n;
    while (tmp > 1) { tmp >>= 1; log2_n++; }

    /* Integer log₃ approximation */
    int log3_n = 0;
    tmp = n;
    while (tmp > 1) { tmp /= 3; log3_n++; }

    /* Economy = digits × radix: binary = log2(n) * 2, ternary = log3(n) * 3 */
    int bin_economy  = log2_n * 2;
    int tern_economy = log3_n * 3;

    if (bin_economy == 0) return 1000;

    /* Return ternary_economy / binary_economy × 1000
     * < 1000 means ternary is more efficient */
    return (tern_economy * 1000) / bin_economy;
}

int art9_get_cpi(const art9_state_t *st) {
    if (!st || st->instructions_retired == 0) return 0;
    return (int)(((int64_t)st->cycles * 1000) / st->instructions_retired);
}

int art9_get_dmips(const art9_state_t *st, int freq_mhz) {
    if (!st || st->instructions_retired == 0 || freq_mhz <= 0) return 0;

    /* DMIPS = freq / CPI (approx) */
    int cpi_x1000 = art9_get_cpi(st);
    if (cpi_x1000 == 0) return 0;

    /* DMIPS = (freq_mhz * 1000000) / (cpi_x1000 / 1000) / 1757 (Dhrystone factor)
     * Simplified: DMIPS ≈ freq_mhz * 1000 / cpi_x1000 */
    return (freq_mhz * 1000) / cpi_x1000;
}
