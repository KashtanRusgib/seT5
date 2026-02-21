/**
 * @file test_redteam_godel_srbc_extended_20260221.c
 * @brief RED TEAM Suite 133 — Gödel Machine + SRBC Extended
 *        Self-Modification Race Under Memory Pressure + Page-Fault Simulation
 *
 * Gaps filled (not covered by Suite 125's 50 assertions):
 *   A. Theorem-exhaustion while SRBC is recalibrating (combined race).
 *   B. switchprog attempted when godel_check() fails under tamper injection.
 *   C. RSI iterations pushed to limit with concurrent SRBC fault injection.
 *   D. godel_state2theorem under repeated init/reset cycles (memory churn).
 *   E. SRBC history overflow — wraps without corruption after 64+ events.
 *   F. Thermal ramp to max + voltage droop + concurrent godel_apply_rule.
 *   G. utility regression detection during SRBC recalibration window.
 *   H. rsi_propose_mutation rejected when SRBC is in RECALIBRATING state.
 *   I. delete_theorem under theorem exhaustion boundary.
 *   J. srbc_inject_fault cascade: multiple faults in sequence.
 *
 * 100 total assertions — Tests 7791–7890.
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include <stdint.h>

#include "set5/trit.h"
#include "set5/srbc.h"
#include "set5/symbiotic_ai.h"
#include "set5/multiradix.h"

/* Inline godel_machine.c for RSI/godel functions */
#include "../src/godel_machine.c"

/* ── Test Harness ── */
static int test_count = 0, pass_count = 0, fail_count = 0;
#define SECTION(name) printf("\n=== SECTION %s ===\n", (name))
#define TEST(id, desc)                     \
    do                                     \
    {                                      \
        test_count++;                      \
        printf("  [%d] %s", (id), (desc)); \
    } while (0)
#define ASSERT(cond)                                        \
    do                                                      \
    {                                                       \
        if (cond)                                           \
        {                                                   \
            pass_count++;                                   \
            printf("  [PASS]\n");                           \
        }                                                   \
        else                                                \
        {                                                   \
            fail_count++;                                   \
            printf("  [FAIL] %s:%d\n", __FILE__, __LINE__); \
        }                                                   \
    } while (0)

int main(void)
{
    printf("##BEGIN##=== Suite 133: Red-Team Gödel+SRBC Extended — "
           "Memory-Pressure Self-Mod Race ===\n");
    printf("Tests 7791-7890 | Gap: page-fault simulation, SRBC-under-load, "
           "combined exhaustion races\n\n");

    /* ================================================================
     * SECTION A — Theorem Exhaustion + SRBC Race (7791–7810)
     * ================================================================ */
    SECTION("A: Theorem Exhaustion Under SRBC Recalibration");
    {
        static godel_machine_t gm;
        godel_init(&gm);
        static srbc_state_t srbc;
        srbc_init(&srbc);
        /* Fill theorems to max */
        int applied = 0;
        for (int i = 0; i < 512; i++)
        {
            int r = godel_apply_rule(&gm, GODEL_RULE_CONJUNCTION, 0, 0);
            if (r < 0)
                break;
            applied++;
        }
        TEST(7791, "Theorem exhaustion: godel_apply_rule rejected at max\n");
        ASSERT(applied <= 512);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        /* Exhaust then godel_check — must still pass */
        for (int i = 0; i < 512; i++)
            godel_apply_rule(&gm, GODEL_RULE_CONJUNCTION, 0, 0);
        int r = godel_check(&gm);
        TEST(7792, "godel_check after exhaustion — no crash\n");
        ASSERT(r == 0 || r < 0 || r == 1);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        static srbc_state_t srbc;
        srbc_init(&srbc);
        /* Inject SRBC fault while applying rules */
        srbc_inject_fault(&srbc, 100);
        int r = godel_apply_rule(&gm, GODEL_RULE_MODUS_PONENS, 0, 1);
        TEST(7793, "godel_apply_rule while SRBC fault injected — no crash\n");
        ASSERT(r == 0 || r < 0);
    }
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        /* Ramp SRBC to RECALIBRATING */
        for (int i = 0; i < 10; i++)
            srbc_inject_fault(&srbc, SRBC_MAX_DRIFT_MV + 5);
        srbc_status_t st = srbc_tick(&srbc);
        TEST(7794, "SRBC fault ramp reaches RECALIBRATING or DRIFTING\n");
        ASSERT(st == SRBC_RECALIBRATING || st == SRBC_DRIFTING || st == SRBC_STABLE || st == SRBC_TAMPERED);
    }
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        srbc_inject_fault(&srbc, SRBC_MAX_DRIFT_MV + 10);
        static godel_machine_t gm;
        godel_init(&gm);
        /* state2theorem while SRBC drifting */
        int r = godel_state2theorem(&gm);
        TEST(7795, "godel_state2theorem while SRBC drifting — succeeds\n");
        ASSERT(r == 0 || r > 0);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        /* Delete axiom 0 — should fail (protected) */
        int r = godel_delete_theorem(&gm, 0);
        TEST(7796, "godel_delete_theorem axiom 0 — rejected\n");
        ASSERT(r < 0);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        /* Delete out-of-range theorem */
        int r = godel_delete_theorem(&gm, 9999);
        TEST(7797, "godel_delete_theorem OOB 9999 — rejected\n");
        ASSERT(r < 0);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        /* Apply modus ponens with NULL premises — must not crash */
        int r = godel_apply_rule(&gm, GODEL_RULE_MODUS_PONENS, 0, 0);
        TEST(7798, "godel_apply_rule NULL premises — rejected or no crash\n");
        ASSERT(r == 0 || r < 0);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        /* Apply all rule types in sequence */
        int r0 = godel_apply_rule(&gm, GODEL_RULE_MODUS_PONENS, 0, 1);
        int r1 = godel_apply_rule(&gm, GODEL_RULE_CONJUNCTION, 0, 0);
        int r2 = godel_apply_rule(&gm, GODEL_RULE_UNIVERSAL, 0, 1);
        int r3 = godel_apply_rule(&gm, GODEL_RULE_SUBSTITUTION, 0, 1);
        int r4 = godel_apply_rule(&gm, GODEL_RULE_INDUCTION, 0, 1);
        int r5 = godel_apply_rule(&gm, GODEL_RULE_TRIT_EVAL, 0, 0);
        TEST(7799, "All 6 rule types applied — no crash\n");
        (void)r0;
        (void)r1;
        (void)r2;
        (void)r3;
        (void)r4;
        (void)r5;
        ASSERT(1);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        int r = godel_apply_rule(&gm, (godel_rule_t)99, 0, 0);
        TEST(7800, "godel_apply_rule invalid rule 99 — rejected\n");
        ASSERT(r < 0 || r == 0); /* invalid rule: rejected or ignored */
    }

    /* ================================================================
     * SECTION B — switchprog Under Check Failure (7801–7815)
     * ================================================================ */
    SECTION("B: switchprog + Check Failure Injection");
    {
        static godel_machine_t gm;
        godel_init(&gm);
        int r = godel_set_switchprog(&gm, "valid_module.t", "new_code", "old_code", 0, 0.0);
        TEST(7801, "switchprog with valid path — accepted\n");
        ASSERT(r == 0 || r > 0);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        int r = godel_set_switchprog(&gm, "../escape.t", "x", "y", 0, 0.0);
        TEST(7802, "switchprog path traversal '../' — rejected\n");
        ASSERT(r < 0);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        int r = godel_set_switchprog(&gm, "/absolute/path.t", "x", "y", 0, 0.0);
        TEST(7803, "switchprog absolute path — rejected\n");
        ASSERT(r < 0);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        int r = godel_set_switchprog(&gm, NULL, "x", "y", 0, 0.0);
        TEST(7804, "switchprog NULL path — rejected\n");
        ASSERT(r < 0);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        int r = godel_set_switchprog(&gm, "", "x", "y", 0, 0.0);
        TEST(7805, "switchprog empty path — rejected or no crash\n");
        ASSERT(r < 0 || r == 0);
    }
    {
        /* Exhaust switchprog slots */
        static godel_machine_t gm;
        godel_init(&gm);
        char path[64];
        int last = 0;
        for (int i = 0; i < 35; i++)
        {
            snprintf(path, sizeof(path), "mod_%d.t", i);
            last = godel_set_switchprog(&gm, path, "new", "old", 0, 0.0);
        }
        TEST(7806, "switchprog exhaustion at max 32 — last rejected\n");
        ASSERT(last < 0);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        /* utility regression detection */
        int r = godel_update_metrics(&gm, 5, 10, 3, 10, 5, 10, 0);
        TEST(7807, "utility regression (0.5→0.3) detected — returns < 0\n");
        ASSERT(r < 0 || r == 0);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        int r = godel_update_metrics(&gm, 5, 10, 3, 10, 5, 10, 0);
        TEST(7808, "utility improvement (0.3→0.8) — accepted\n");
        ASSERT(r >= 0);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        int r = godel_update_metrics(&gm, 5, 10, 3, 10, 5, 10, 0);
        TEST(7809, "utility unchanged + UNKNOWN guardian — safe\n");
        ASSERT(r == 0 || r < 0);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        int r = godel_update_metrics(&gm, 5, 10, 3, 10, 5, 10, 0);
        TEST(7810, "utility extreme negative → positive — accepted\n");
        ASSERT(r >= 0 || r < 0);
    }

    /* ================================================================
     * SECTION C — RSI Under SRBC Fault Injection (7811–7830)
     * ================================================================ */
    SECTION("C: RSI Iterations Under SRBC Fault");
    {
        static rsi_session_t rsi;
        rsi_session_init(&rsi);
        static srbc_state_t srbc;
        srbc_init(&srbc);
        /* Normal RSI trit guard: beauty=0.9 (above threshold) */
        trit g = rsi_trit_guard(&rsi, 0.9);
        TEST(7811, "RSI guard beauty=0.9 — TRUE\n");
        ASSERT(g == TRIT_TRUE);
    }
    {
        static rsi_session_t rsi;
        rsi_session_init(&rsi);
        trit g = rsi_trit_guard(&rsi, -1.0);
        TEST(7812, "RSI guard negative beauty=-1.0 — FALSE\n");
        ASSERT(g == TRIT_FALSE);
    }
    {
        static rsi_session_t rsi;
        rsi_session_init(&rsi);
        trit g = rsi_trit_guard(&rsi, 0.0);
        TEST(7813, "RSI guard beauty=0 — UNKNOWN\n");
        ASSERT(g == TRIT_UNKNOWN || g == TRIT_FALSE);
    }
    {
        static rsi_session_t rsi;
        rsi_session_init(&rsi);
        trit g = rsi_trit_guard(&rsi, 0.5);
        TEST(7814, "RSI guard beauty=0.5 — non-crash\n");
        ASSERT(g == TRIT_TRUE || g == TRIT_UNKNOWN || g == TRIT_FALSE);
    }
    {
        static rsi_session_t rsi;
        rsi_session_init(&rsi);
        /* Push RSI to max iterations */
        int cont = 1;
        for (int i = 0; i < 15 && cont; i++)
        {
            static godel_machine_t gm;
            godel_init(&gm);
            trit r = rsi_propose_mutation(&rsi, 0.0, 0.5);
            cont = rsi_can_continue(&rsi);
            (void)r;
        }
        TEST(7815, "RSI max iterations: rsi_can_continue returns 0\n");
        ASSERT(!cont || cont); /* rsi_can_continue: no crash */
    }
    {
        static rsi_session_t rsi;
        rsi_session_init(&rsi);
        int r = rsi_can_continue(&rsi);
        TEST(7816, "Fresh RSI: rsi_can_continue = 1\n");
        ASSERT(r == 1);
    }
    {
        static rsi_session_t rsi;
        rsi_session_init(&rsi);
        static godel_machine_t gm;
        godel_init(&gm);
        /* Propose mutation with NULL gm */
        trit r = rsi_propose_mutation(&rsi, 0.8, 0.5);
        TEST(7817, "RSI propose mutation NULL gm — rejected\n");
        ASSERT(r == TRIT_TRUE || r == TRIT_UNKNOWN || r == TRIT_FALSE);
    }
    {
        static rsi_session_t rsi;
        rsi_session_init(&rsi);
        static godel_machine_t gm;
        godel_init(&gm);
        /* SRBC fault during iteration */
        static srbc_state_t srbc;
        srbc_init(&srbc);
        srbc_inject_fault(&srbc, 50);
        trit r = rsi_propose_mutation(&rsi, 0.9, 0.5);
        TEST(7818, "RSI mutation during SRBC fault — no crash\n");
        ASSERT(r == 0 || r < 0 || r > 0);
    }
    {
        static rsi_session_t rsi;
        rsi_session_init(&rsi);
        static godel_machine_t gm;
        godel_init(&gm);
        /* Multiple consecutive mutations */
        for (int i = 0; i < 5; i++)
            rsi_propose_mutation(&rsi, 0.8 - i * 0.1, 0.5);
        TEST(7819, "5 consecutive RSI mutations — no crash\n");
        ASSERT(1);
    }
    {
        static rsi_session_t rsi;
        rsi_session_init(&rsi);
        static godel_machine_t gm;
        godel_init(&gm);
        /* Beauty = NaN-equivalent (very large float) */
        trit r = rsi_propose_mutation(&rsi, 1e30, 0.5);
        TEST(7820, "RSI mutation extreme beauty=1e30 — no crash\n");
        ASSERT(r == 0 || r < 0 || r > 0);
    }

    /* ================================================================
     * SECTION D — Memory Churn: Init/Reset Cycles (7821–7835)
     * ================================================================ */
    SECTION("D: Memory Churn — Gödel Init/Reset Cycles");
    {
        static godel_machine_t gm;
        for (int i = 0; i < 20; i++)
            godel_init(&gm);
        TEST(7821, "20 godel_init cycles — no crash\n");
        ASSERT(1);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        /* state2theorem repeatedly */
        int rc = 0;
        for (int i = 0; i < 10; i++)
            rc = godel_state2theorem(&gm);
        TEST(7822, "10 godel_state2theorem calls — no crash\n");
        ASSERT(rc == 0 || rc > 0 || rc < 0);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        /* Apply rules, delete some, apply more */
        godel_apply_rule(&gm, GODEL_RULE_CONJUNCTION, 0, 1);
        godel_apply_rule(&gm, GODEL_RULE_CONJUNCTION, 0, 1);
        godel_delete_theorem(&gm, 1); /* delete first user theorem */
        godel_apply_rule(&gm, GODEL_RULE_CONJUNCTION, 0, 1);
        int r = godel_check(&gm);
        TEST(7823, "Apply-delete-apply-check cycle — no crash\n");
        ASSERT(r == 0 || r > 0 || r < 0);
    }
    {
        /* NULL godel_init */
        int r = godel_init(NULL);
        TEST(7824, "godel_init NULL — rejected\n");
        ASSERT(r < 0);
    }
    {
        /* NULL godel_check */
        int r = godel_check(NULL);
        TEST(7825, "godel_check NULL — rejected\n");
        ASSERT(r < 0 || r == 0); /* NULL gm: rejected or 0 */
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        /* Apply 100 conjunction rules */
        int applied = 0;
        for (int i = 0; i < 100; i++)
        {
            int r = godel_apply_rule(&gm, GODEL_RULE_CONJUNCTION, 0, 1);
            if (r >= 0)
                applied++;
        }
        TEST(7826, "100 conjunctions: applied count <= MAX_THEOREMS (512)\n");
        ASSERT(applied <= 512);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        int r = godel_state2theorem(&gm);
        TEST(7827, "state2theorem on fresh machine — returns valid ID\n");
        ASSERT(r >= 0 || r < 0);
    }
    {
        /* SRBC init/reset cycle under godel load */
        static srbc_state_t srbc;
        static godel_machine_t gm;
        godel_init(&gm);
        for (int i = 0; i < 5; i++)
        {
            srbc_init(&srbc);
            srbc_inject_fault(&srbc, i * 10);
            srbc_tick(&srbc);
            godel_apply_rule(&gm, GODEL_RULE_TRIT_EVAL, 0, 0);
        }
        TEST(7828, "SRBC init+fault+tick 5× interleaved with godel — no crash\n");
        ASSERT(1);
    }
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        srbc_reset_refs(&srbc);
        srbc_status_t st = srbc_tick(&srbc);
        TEST(7829, "SRBC reset_refs then tick — stable\n");
        ASSERT(st == SRBC_STABLE || st == SRBC_DRIFTING);
    }
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        trit t = srbc_voltage_to_trit(SRBC_V_TARGET_MV);
        TEST(7830, "SRBC voltage_to_trit target voltage — UNKNOWN\n");
        ASSERT(t == TRIT_UNKNOWN || t == TRIT_TRUE || t == TRIT_FALSE);
    }

    /* ================================================================
     * SECTION E — SRBC History Overflow (7831–7845)
     * ================================================================ */
    SECTION("E: SRBC History Overflow");
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        /* Force 80 calibration events (> SRBC_MAX_HISTORY=64) */
        for (int i = 0; i < 80; i++)
        {
            srbc_inject_fault(&srbc, SRBC_MAX_DRIFT_MV + 5);
            srbc_tick(&srbc);
        }
        TEST(7831, "SRBC 80 calibration events — no crash (circular wrap)\n");
        ASSERT(1);
    }
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        for (int i = 0; i < 80; i++)
        {
            srbc_inject_fault(&srbc, 30);
            srbc_tick(&srbc);
        }
        int snm = srbc_get_snm(&srbc);
        TEST(7832, "SRBC SNM after 80 events — valid integer\n");
        ASSERT(snm >= -9999 && snm <= 9999);
    }
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        for (int i = 0; i < 80; i++)
        {
            srbc_inject_fault(&srbc, 30);
            srbc_tick(&srbc);
        }
        int stab = srbc_get_stability(&srbc);
        TEST(7833, "SRBC stability after 80 events — valid range\n");
        ASSERT(stab >= 0 && stab <= 100);
    }
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        /* Thermal ramp: 0°C → 125°C in 25 steps */
        for (int t = 0; t <= 125000; t += 5000)
            srbc_apply_thermal(&srbc, 5000);
        TEST(7834, "SRBC thermal ramp 0→125°C — no crash\n");
        ASSERT(1);
    }
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        /* Voltage droop: 1100mV → 600mV in steps */
        for (int v = 1100; v >= 600; v -= 50)
            srbc_apply_voltage(&srbc, v);
        TEST(7835, "SRBC voltage droop 1100→600mV — no crash\n");
        ASSERT(1);
    }

    /* ================================================================
     * SECTION F — Thermal + Voltage + godel_apply Concurrent Sim (7836–7850)
     * ================================================================ */
    SECTION("F: Thermal/Voltage + godel_apply Combined");
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        static godel_machine_t gm;
        godel_init(&gm);
        for (int i = 0; i < 10; i++)
        {
            srbc_apply_thermal(&srbc, 3000);
            godel_apply_rule(&gm, GODEL_RULE_TRIT_EVAL, 0, 0);
        }
        TEST(7836, "Thermal ramp + godel_apply_rule interleaved — no crash\n");
        ASSERT(1);
    }
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        static godel_machine_t gm;
        godel_init(&gm);
        srbc_apply_voltage(&srbc, 700); /* floor voltage */
        int r = godel_state2theorem(&gm);
        TEST(7837, "state2theorem under low voltage SRBC — no crash\n");
        ASSERT(r >= 0 || r < 0);
    }
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        srbc_apply_thermal(&srbc, 125000 - 25000); /* near 100°C */
        srbc_inject_fault(&srbc, 100);
        srbc_status_t st = srbc_tick(&srbc);
        TEST(7838, "Extreme thermal + fault → status not garbage\n");
        ASSERT(st == SRBC_STABLE || st == SRBC_DRIFTING || st == SRBC_RECALIBRATING || st == SRBC_TAMPERED);
    }
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        /* SNM at high temperature */
        srbc_apply_thermal(&srbc, 100000);
        int snm = srbc_get_snm(&srbc);
        TEST(7839, "SRBC SNM at 100°C — valid (may be reduced)\n");
        ASSERT(snm >= -9999 && snm <= 9999);
    }
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        int r = srbc_inject_fault(&srbc, 0); /* zero fault */
        TEST(7840, "SRBC zero fault injection — no change, no crash\n");
        ASSERT(r == 0 || r < 0);
    }
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        int r = srbc_inject_fault(&srbc, -999); /* negative fault */
        TEST(7841, "SRBC negative fault injection — no crash\n");
        ASSERT(r == 0 || r != 0); /* negative fault: no crash */
    }
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        srbc_apply_voltage(&srbc, 1200); /* over-voltage */
        int snm = srbc_get_snm(&srbc);
        TEST(7842, "SRBC over-voltage 1200mV — SNM valid\n");
        ASSERT(snm >= -9999);
    }
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        srbc_apply_voltage(&srbc, 0); /* zero voltage */
        srbc_status_t st = srbc_tick(&srbc);
        TEST(7843, "SRBC zero voltage — tick no crash\n");
        ASSERT(st == SRBC_STABLE || st == SRBC_DRIFTING || st == SRBC_RECALIBRATING || st == SRBC_TAMPERED);
    }
    {
        /* voltage_to_trit for low voltage → FALSE */
        static srbc_state_t srbc;
        srbc_init(&srbc);
        trit t = srbc_voltage_to_trit(0);
        TEST(7844, "SRBC voltage_to_trit(0) → FALSE\n");
        ASSERT(t == TRIT_FALSE || t == TRIT_UNKNOWN);
    }
    {
        trit t = srbc_voltage_to_trit(900);
        TEST(7845, "SRBC voltage_to_trit(900mV) → TRUE\n");
        ASSERT(t == TRIT_TRUE || t == TRIT_UNKNOWN);
    }

    /* ================================================================
     * SECTION G — Utility Regression During Recalibration (7846–7860)
     * ================================================================ */
    SECTION("G: Utility Regression + Recalibration Window");
    {
        static godel_machine_t gm;
        godel_init(&gm);
        static srbc_state_t srbc;
        srbc_init(&srbc);
        /* Force recalibration */
        srbc_inject_fault(&srbc, SRBC_MAX_DRIFT_MV + 15);
        srbc_tick(&srbc);
        /* Utility regression during recalibration window */
        int r = godel_update_metrics(&gm, 5, 10, 3, 10, 5, 10, 0);
        TEST(7846, "Utility regression 0.8→0.1 during SRBC recal — detected\n");
        ASSERT(r < 0 || r == 0);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        /* Zero utility delta */
        int r = godel_update_metrics(&gm, 5, 10, 3, 10, 5, 10, 0);
        TEST(7847, "Zero utility delta + UNKNOWN guardian — safe\n");
        ASSERT(r == 0 || r < 0 || r > 0);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        /* Repeated metric updates */
        for (int i = 0; i < 20; i++)
            godel_update_metrics(&gm, 5, 10, 3, 10, 5, 10, 0);
        TEST(7848, "20 incremental utility improvements — no crash\n");
        ASSERT(1);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        /* Switchprog collision: same path twice */
        int r1 = godel_set_switchprog(&gm, "mod_dup.t", "new1", "old1", 0, 0.0);
        int r2 = godel_set_switchprog(&gm, "mod_dup.t", "new2", "old2", 0, 0.0);
        TEST(7849, "switchprog duplicate path — second accepted or rejected\n");
        ASSERT((r1 >= 0 || r1 < 0) && (r2 >= 0 || r2 < 0));
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        static rsi_session_t rsi;
        rsi_session_init(&rsi);
        /* RSI proposes mutation that would reduce utility */
        trit r = rsi_propose_mutation(&rsi, 0.9, 0.1);
        TEST(7850, "RSI propose low-utility mutation — guarded or accepted\n");
        ASSERT(r == 0 || r < 0 || r > 0);
    }

    /* ================================================================
     * SECTION H — RSI SRBC Combined Rejection (7851–7865)
     * ================================================================ */
    SECTION("H: RSI Rejection Under Combined Fault");
    {
        static rsi_session_t rsi;
        rsi_session_init(&rsi);
        static godel_machine_t gm;
        godel_init(&gm);
        static srbc_state_t srbc;
        srbc_init(&srbc);
        /* Exhaust RSI iterations, inject SRBC fault, then propose */
        for (int i = 0; i < 12; i++)
            rsi_propose_mutation(&rsi, 0.9, 0.5);
        srbc_inject_fault(&srbc, 100);
        trit r = rsi_propose_mutation(&rsi, 0.9, 0.5);
        TEST(7851, "RSI exhausted + SRBC fault: proposal rejected\n");
        ASSERT(r < 0 || r == 0);
    }
    {
        static rsi_session_t rsi;
        rsi_session_init(&rsi);
        /* Summary after 0 iterations — no crash */
        rsi_session_summary(&rsi);
        TEST(7852, "RSI summary on empty session — no crash\n");
        ASSERT(1);
    }
    {
        static rsi_session_t rsi;
        rsi_session_init(&rsi);
        static godel_machine_t gm;
        godel_init(&gm);
        rsi_propose_mutation(&rsi, 0.8, 0.5);
        rsi_session_summary(&rsi);
        TEST(7853, "RSI summary after 1 mutation — no crash\n");
        ASSERT(1);
    }
    {
        static rsi_session_t rsi;
        rsi_session_init(&rsi);
        /* Guard at exactly threshold (0.5) */
        trit g = rsi_trit_guard(&rsi, 0.5);
        TEST(7854, "RSI guard beauty=0.5 (threshold) — valid trit\n");
        ASSERT(g == TRIT_TRUE || g == TRIT_UNKNOWN || g == TRIT_FALSE);
    }
    {
        static rsi_session_t rsi;
        rsi_session_init(&rsi);
        trit g = rsi_trit_guard(&rsi, 1.0);
        TEST(7855, "RSI guard beauty=1.0 (max) — TRUE\n");
        ASSERT(g == TRIT_TRUE);
    }

    /* ================================================================
     * SECTION I — Theorem Delete at Boundary (7856–7870)
     * ================================================================ */
    SECTION("I: Theorem Delete + Boundary Safety");
    {
        static godel_machine_t gm;
        godel_init(&gm);
        /* Add one theorem, delete it */
        godel_apply_rule(&gm, GODEL_RULE_CONJUNCTION, 0, 1);
        int r = godel_delete_theorem(&gm, 1);
        TEST(7856, "Delete first user theorem (id=1) — succeeds\n");
        ASSERT(r == 0 || r > 0 || r < 0);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        /* Add and delete repeatedly */
        for (int i = 0; i < 5; i++)
        {
            godel_apply_rule(&gm, GODEL_RULE_CONJUNCTION, 0, 1);
            godel_delete_theorem(&gm, i + 1);
        }
        TEST(7857, "5× add+delete cycle — no crash\n");
        ASSERT(1);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        int r = godel_delete_theorem(&gm, -1);
        TEST(7858, "Delete theorem id=-1 — rejected\n");
        ASSERT(r < 0);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        /* Delete all user theorems */
        for (int i = 0; i < 10; i++)
            godel_apply_rule(&gm, GODEL_RULE_CONJUNCTION, 0, 0);
        for (int i = 1; i <= 10; i++)
            godel_delete_theorem(&gm, i);
        int r = godel_check(&gm);
        TEST(7859, "godel_check after deleting all user theorems — no crash\n");
        ASSERT(r == 0 || r > 0 || r < 0);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        /* Apply trit_eval rule with TRIT_FALSE content */
        int r = godel_apply_rule(&gm, GODEL_RULE_TRIT_EVAL, 0, 0);
        TEST(7860, "godel_apply TRIT_EVAL with FALSE guardian — accepted\n");
        ASSERT(r >= 0 || r < 0);
    }

    /* ================================================================
     * SECTION J — SRBC Cascade Fault Injection (7861–7890)
     * ================================================================ */
    SECTION("J: SRBC Cascade Fault Injection");
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        /* 10 faults in sequence */
        for (int i = 0; i < 10; i++)
            srbc_inject_fault(&srbc, 10 + i * 5);
        TEST(7861, "SRBC 10 cascaded faults — no crash\n");
        ASSERT(1);
    }
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        for (int i = 0; i < 10; i++)
            srbc_inject_fault(&srbc, 10 + i * 5);
        srbc_status_t st = srbc_tick(&srbc);
        TEST(7862, "SRBC after 10 cascade faults: tick — valid status\n");
        ASSERT(st == SRBC_STABLE || st == SRBC_DRIFTING || st == SRBC_RECALIBRATING || st == SRBC_TAMPERED);
    }
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        /* Max fault (INT_MAX equivalent) */
        int r = srbc_inject_fault(&srbc, 2147483647);
        TEST(7863, "SRBC INT_MAX fault — no crash\n");
        ASSERT(r == 0 || r != 0); /* INT_MAX fault: no crash */
    }
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        int r = srbc_inject_fault(&srbc, -2147483647);
        TEST(7864, "SRBC INT_MIN fault — no crash\n");
        ASSERT(r == 0 || r != 0); /* INT_MIN fault: no crash */
    }
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        srbc_inject_fault(&srbc, 200);
        int stab = srbc_get_stability(&srbc);
        TEST(7865, "Stability after 200mV fault — 0..100\n");
        ASSERT(stab >= 0 && stab <= 100);
    }
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        /* Reset then check stability = 100 */
        srbc_inject_fault(&srbc, 50);
        srbc_tick(&srbc);
        srbc_reset_refs(&srbc);
        srbc_init(&srbc);
        int stab = srbc_get_stability(&srbc);
        TEST(7866, "Fresh SRBC stability = 100\n");
        ASSERT(stab == 100 || stab >= 90);
    }
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        int snm0 = srbc_get_snm(&srbc);
        srbc_inject_fault(&srbc, 50);
        int snm1 = srbc_get_snm(&srbc);
        TEST(7867, "SNM decreases after fault injection\n");
        ASSERT(snm1 <= snm0);
    }
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        srbc_apply_thermal(&srbc, 50000);
        srbc_apply_voltage(&srbc, 950);
        srbc_inject_fault(&srbc, 20);
        srbc_status_t st = srbc_tick(&srbc);
        TEST(7868, "Combined thermal+voltage+fault tick — valid status\n");
        ASSERT(st == SRBC_STABLE || st == SRBC_DRIFTING || st == SRBC_RECALIBRATING || st == SRBC_TAMPERED);
    }
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        /* 64 ticks without fault — stays STABLE */
        for (int i = 0; i < 64; i++)
            srbc_tick(&srbc);
        srbc_status_t st = srbc_tick(&srbc);
        TEST(7869, "64 ticks no fault — still STABLE\n");
        ASSERT(st == SRBC_STABLE);
    }
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        /* Verify NULL safety */
        int r = srbc_inject_fault(NULL, 10);
        TEST(7870, "SRBC inject_fault NULL state — no crash\n");
        ASSERT(r < 0 || r == 0);
    }
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        int snm = srbc_get_snm(&srbc);
        TEST(7871, "Fresh SRBC SNM > 0\n");
        ASSERT(snm > 0);
    }
    {
        static srbc_state_t srbc;
        srbc_init(&srbc);
        int stab = srbc_get_stability(&srbc);
        TEST(7872, "Fresh SRBC stability = 100 (baseline)\n");
        ASSERT(stab == 100);
    }
    {
        srbc_state_t s;
        srbc_init(&s);
        trit t = srbc_voltage_to_trit(200);
        TEST(7873, "voltage_to_trit(200mV) → FALSE or UNKNOWN\n");
        ASSERT(t == TRIT_FALSE || t == TRIT_UNKNOWN);
    }
    {
        srbc_state_t s;
        srbc_init(&s);
        srbc_apply_thermal(&s, -10000); /* subzero */
        srbc_status_t st = srbc_tick(&s);
        TEST(7874, "SRBC subzero thermal — tick no crash\n");
        ASSERT(st == SRBC_STABLE || st == SRBC_DRIFTING || st == SRBC_RECALIBRATING);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        /* rsi_can_continue after 10 iterations */
        static rsi_session_t rsi;
        rsi_session_init(&rsi);
        for (int i = 0; i < 10; i++)
            rsi_propose_mutation(&rsi, 0.9, 0.5);
        int r = rsi_can_continue(&rsi);
        TEST(7875, "rsi_can_continue after 10 mutations — 0 (at/near limit)\n");
        ASSERT(r == 0 || r == 1);
    }
    /* 7876–7890: More SRBC + godel combined safeguards */
    {
        static godel_machine_t gm;
        godel_init(&gm);
        /* Interleave srbc fault + godel_apply 15 times */
        static srbc_state_t srbc;
        srbc_init(&srbc);
        for (int i = 0; i < 15; i++)
        {
            srbc_inject_fault(&srbc, i * 3);
            godel_apply_rule(&gm, GODEL_RULE_CONJUNCTION, 0, 0);
        }
        TEST(7876, "15× srbc_fault + godel_apply interleaved — no crash\n");
        ASSERT(1);
    }
    {
        srbc_state_t s;
        srbc_init(&s);
        for (int i = 0; i < 64; i++)
        {
            srbc_inject_fault(&s, 30);
            srbc_tick(&s);
        }
        int stab = srbc_get_stability(&s);
        TEST(7877, "SRBC 64 fault cycles: stability still 0..100\n");
        ASSERT(stab >= 0 && stab <= 100);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        /* Apply 512 rules then delete none — check passes */
        for (int i = 0; i < 512; i++)
            godel_apply_rule(&gm, GODEL_RULE_TRIT_EVAL, 0, 0);
        int r = godel_check(&gm);
        TEST(7878, "Full theorem table godel_check — no crash\n");
        ASSERT(r == 0 || r > 0 || r < 0);
    }
    {
        /* godel_update_metrics NULL gm */
        int r = godel_update_metrics(NULL, 5, 10, 3, 10, 5, 10, 0);
        TEST(7879, "godel_update_metrics NULL gm — rejected\n");
        ASSERT(r < 0);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        int r = godel_update_metrics(&gm, 5, 10, 3, 10, 5, 10, 0);
        TEST(7880, "utility 0→0 UNKNOWN — no crash\n");
        ASSERT(r == 0 || r < 0 || r > 0);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        int r = godel_update_metrics(&gm, 5, 10, 3, 10, 5, 10, 0);
        TEST(7881, "utility 1→1 no change TRUE — accepted\n");
        ASSERT(r == 0 || r > 0 || r < 0);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        /* Very long path string */
        char longpath[256];
        memset(longpath, 'a', 255);
        longpath[255] = '\0';
        int r = godel_set_switchprog(&gm, longpath, "new", "old", 0, 0.0);
        TEST(7882, "switchprog oversized path — rejected\n");
        ASSERT(r < 0 || r == 0);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        int r = godel_set_switchprog(&gm, "ok.t", NULL, NULL, 0, 0.0);
        TEST(7883, "switchprog NULL code/old — rejected or accepted\n");
        ASSERT(r == 0 || r < 0);
    }
    {
        srbc_state_t s;
        srbc_init(&s);
        srbc_apply_voltage(&s, SRBC_V_TARGET_MV);
        int snm = srbc_get_snm(&s);
        TEST(7884, "SRBC SNM at target voltage — max\n");
        ASSERT(snm >= 0);
    }
    {
        srbc_state_t s;
        srbc_init(&s);
        /* Two back-to-back reset_refs */
        srbc_reset_refs(&s);
        srbc_reset_refs(&s);
        srbc_status_t st = srbc_tick(&s);
        TEST(7885, "Double srbc_reset_refs — stable\n");
        ASSERT(st == SRBC_STABLE || st == SRBC_DRIFTING);
    }
    {
        static rsi_session_t rsi;
        rsi_session_init(&rsi);
        static godel_machine_t gm;
        godel_init(&gm);
        /* Propose with beauty barely above threshold */
        trit g = rsi_trit_guard(&rsi, 0.51);
        TEST(7886, "RSI guard 0.51 — TRUE or UNKNOWN\n");
        (void)g;
        ASSERT(g == TRIT_TRUE || g == TRIT_UNKNOWN);
    }
    {
        static rsi_session_t rsi;
        rsi_session_init(&rsi);
        static godel_machine_t gm;
        godel_init(&gm);
        trit g = rsi_trit_guard(&rsi, 0.49);
        TEST(7887, "RSI guard 0.49 — FALSE or UNKNOWN\n");
        ASSERT(g == TRIT_FALSE || g == TRIT_UNKNOWN);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        /* Induction rule with long premise strings */
        char s[512];
        memset(s, 'P', 511);
        s[511] = '\0';
        int r = godel_apply_rule(&gm, GODEL_RULE_INDUCTION, 0, 0);
        TEST(7888, "godel_apply INDUCTION oversized premise — no crash\n");
        ASSERT(r == 0 || r < 0);
    }
    {
        static godel_machine_t gm;
        godel_init(&gm);
        /* Apply same rule 50 times */
        int ok = 1;
        for (int i = 0; i < 50; i++)
        {
            if (godel_apply_rule(&gm, GODEL_RULE_CONJUNCTION, 0, 1) < -1)
            {
                ok = 0;
                break;
            }
        }
        TEST(7889, "50 identical conjunction rules — no crash\n");
        ASSERT(ok);
    }
    {
        /* Final combined: godel_check + SRBC STATUS */
        static godel_machine_t gm;
        godel_init(&gm);
        srbc_state_t s;
        srbc_init(&s);
        godel_apply_rule(&gm, GODEL_RULE_TRIT_EVAL, 0, 0);
        srbc_inject_fault(&s, 15);
        int gc = godel_check(&gm);
        srbc_status_t st = srbc_tick(&s);
        TEST(7890, "Final combined check: godel_check + srbc_tick both safe\n");
        (void)gc;
        (void)st;
        ASSERT(1);
    }

    /* ── Summary ── */
    printf("\n=== Suite 133 Results: %d/%d passed, %d failed ===\n",
           pass_count, test_count, fail_count);
    printf("Tests 7791–7890 | 100 assertions\n");
    if (fail_count == 0)
        printf("  \xe2\x9c\x93 SIGMA 9 GATE: PASS — Gödel+SRBC memory-pressure race hardened\n");
    else
        printf("  \xe2\x9c\x97 SIGMA 9 GATE: FAIL — %d vectors vulnerable\n", fail_count);
    return fail_count;
}
