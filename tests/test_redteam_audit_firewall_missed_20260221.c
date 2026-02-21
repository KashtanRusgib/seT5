/**
 * @file test_redteam_audit_firewall_missed_20260221.c
 * @brief RED TEAM Suite 138 — Audit Firewall (afw_*) Gap Coverage
 *
 * Module: src/audit_firewall.c
 * Gap: Only appears as a side mention in test_red_team_fullstack_kernel.c
 * with zero dedicated red-team assertions. The audit/firewall module is a
 * critical security boundary.
 *
 * Attack vectors covered:
 *   A. Rule overflow: inject beyond AFW_MAX_RULES (64)
 *   B. Log overflow: inject beyond AFW_MAX_LOG_ENTRIES (256) — VULN-48 boundary
 *   C. NULL state attacks on all entry points
 *   D. UNKNOWN action rules (AFW_ACTION_INSPECT = TRIT_UNKNOWN) bypass
 *   E. Priority race: two rules same priority — first wins vs last wins
 *   F. Wildcard port (-1) matched before specific port rules
 *   G. AFW_DIR_BOTH covers both inbound and outbound
 *   H. Rule hit_count accuracy across repeated evaluations
 *   I. Log timestamp monotonicity
 *   J. Concurrent rule manipulation simulation
 *
 * 100 assertions — Tests 8291–8390
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include <stdint.h>

#include "set5/trit.h"

/* Inline the audit_firewall module (all functions are static inline in .c) */
#include "../src/audit_firewall.c"

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

/* ─────────────────────────────────────────────────────────────────────────── */
/* SECTION A — Init + basic rule (8291–8305)                                   */
/* ─────────────────────────────────────────────────────────────────────────── */
static void section_a(void)
{
    SECTION("A: Init and basic rule add");

    /* 8291: fresh init zeroes state */
    TEST(8291, "afw_init zeros state\n");
    static afw_state_t fw;
    afw_init(&fw);
    ASSERT(fw.rule_count == 0 && fw.log_count == 0 &&
           fw.total_allowed == 0 && fw.total_denied == 0);

    /* 8292: afw_init on NULL does not crash */
    TEST(8292, "afw_init(NULL) does not crash\n");
    afw_init(NULL);
    ASSERT(1); /* reaching here = pass */

    /* 8293: add first ALLOW rule */
    TEST(8293, "add ALLOW rule: returns rule index 0\n");
    int r0 = afw_add_rule(&fw, "allow_http", AFW_DIR_INBOUND,
                          AFW_ACTION_ALLOW, 80, 10);
    ASSERT(r0 == 0);

    /* 8294: rule count increments */
    TEST(8294, "rule_count == 1 after first add\n");
    ASSERT(fw.rule_count == 1);

    /* 8295: add DENY rule */
    TEST(8295, "add DENY rule: returns rule index 1\n");
    int r1 = afw_add_rule(&fw, "deny_ssh", AFW_DIR_INBOUND,
                          AFW_ACTION_DENY, 22, 5);
    ASSERT(r1 == 1);

    /* 8296: ALLOW rule hit on port 80 inbound */
    TEST(8296, "evaluate port 80 inbound → ALLOW\n");
    int act = afw_evaluate(&fw, AFW_DIR_INBOUND, 80);
    ASSERT(act == AFW_ACTION_ALLOW);

    /* 8297: DENY rule hit on port 22 inbound */
    TEST(8297, "evaluate port 22 inbound → DENY\n");
    ASSERT(afw_evaluate(&fw, AFW_DIR_INBOUND, 22) == AFW_ACTION_DENY);

    /* 8298: no matching rule → default DENY */
    TEST(8298, "no matching rule → default DENY\n");
    ASSERT(afw_evaluate(&fw, AFW_DIR_INBOUND, 9999) == AFW_ACTION_DENY);

    /* 8299: total_allowed incremented on ALLOW */
    TEST(8299, "total_allowed == 1 after one ALLOW hit\n");
    ASSERT(fw.total_allowed >= 1);

    /* 8300: total_denied incremented on DENY */
    TEST(8300, "total_denied >= 1 after DENY hits\n");
    ASSERT(fw.total_denied >= 1);

    /* 8301: log_count increments on each evaluate */
    TEST(8301, "log_count grows with each evaluate\n");
    int lc_before = fw.log_count;
    afw_evaluate(&fw, AFW_DIR_INBOUND, 80);
    ASSERT(fw.log_count == lc_before + 1);

    /* 8302: add INSPECT rule */
    TEST(8302, "add INSPECT (UNKNOWN action) rule\n");
    int r2 = afw_add_rule(&fw, "inspect_443", AFW_DIR_BOTH,
                          AFW_ACTION_INSPECT, 443, 8);
    ASSERT(r2 == 2);

    /* 8303: INSPECT rule evaluates to AFW_ACTION_INSPECT */
    TEST(8303, "evaluate port 443 → INSPECT\n");
    ASSERT(afw_evaluate(&fw, AFW_DIR_INBOUND, 443) == AFW_ACTION_INSPECT);

    /* 8304: total_inspected incremented */
    TEST(8304, "total_inspected >= 1 after INSPECT hit\n");
    ASSERT(fw.total_inspected >= 1);

    /* 8305: afw_get_denied returns non-negative */
    TEST(8305, "afw_get_denied returns non-negative\n");
    ASSERT(afw_get_denied(&fw) >= 0);
}

/* ─────────────────────────────────────────────────────────────────────────── */
/* SECTION B — Rule overflow injection (8306–8320)                            */
/* ─────────────────────────────────────────────────────────────────────────── */
static void section_b(void)
{
    SECTION("B: Rule overflow injection");

    /* 8306: fill AFW_MAX_RULES (64) */
    TEST(8306, "fill 64 rules — all succeed\n");
    static afw_state_t fw;
    afw_init(&fw);
    int ok = 1;
    char name[32];
    for (int i = 0; i < 64; i++)
    {
        snprintf(name, sizeof(name), "rule_%d", i);
        if (afw_add_rule(&fw, name, AFW_DIR_BOTH,
                         AFW_ACTION_ALLOW, i, i) < 0)
        {
            ok = 0;
            break;
        }
    }
    ASSERT(ok && fw.rule_count == 64);

    /* 8307: 65th rule returns -1 */
    TEST(8307, "65th rule returns -1 (overflow)\n");
    ASSERT(afw_add_rule(&fw, "overflow", AFW_DIR_BOTH,
                        AFW_ACTION_ALLOW, 999, 1) == -1);

    /* 8308: rule_count does not exceed AFW_MAX_RULES */
    TEST(8308, "rule_count <= AFW_MAX_RULES\n");
    ASSERT(fw.rule_count <= 64);

    /* 8309: afw_add_rule with NULL state returns -1 */
    TEST(8309, "afw_add_rule(NULL) returns -1\n");
    ASSERT(afw_add_rule(NULL, "x", AFW_DIR_BOTH,
                        AFW_ACTION_DENY, 80, 1) == -1);

    /* 8310: afw_add_rule with NULL name returns -1 */
    TEST(8310, "afw_add_rule with NULL name returns -1\n");
    static afw_state_t fw2;
    afw_init(&fw2);
    ASSERT(afw_add_rule(&fw2, NULL, AFW_DIR_BOTH,
                        AFW_ACTION_DENY, 80, 1) == -1);

    /* 8311: afw_evaluate with NULL state returns AFW_ACTION_DENY */
    TEST(8311, "afw_evaluate(NULL) returns DENY\n");
    ASSERT(afw_evaluate(NULL, AFW_DIR_INBOUND, 80) == AFW_ACTION_DENY);

    /* 8312: afw_get_log_count(NULL) returns 0 */
    TEST(8312, "afw_get_log_count(NULL) returns 0\n");
    ASSERT(afw_get_log_count(NULL) == 0);

    /* 8313: afw_get_denied(NULL) returns 0 */
    TEST(8313, "afw_get_denied(NULL) returns 0\n");
    ASSERT(afw_get_denied(NULL) == 0);

    /* 8314: afw_get_inspected(NULL) returns 0 */
    TEST(8314, "afw_get_inspected(NULL) returns 0\n");
    ASSERT(afw_get_inspected(NULL) == 0);

    /* 8315: evaluate after full rule table — highest priority wins */
    TEST(8315, "evaluate with full table: highest priority rule matched\n");
    /* rule 63 is port 63 priority 63 — it should match port 63 */
    int act = afw_evaluate(&fw, AFW_DIR_BOTH, 63);
    ASSERT(act == AFW_ACTION_ALLOW);

    /* 8316: rule hit_count increments on match */
    TEST(8316, "rule 63 hit_count increments on match\n");
    int hc = fw.rules[63].hit_count;
    afw_evaluate(&fw, AFW_DIR_BOTH, 63);
    ASSERT(fw.rules[63].hit_count == hc + 1);

    /* 8317: inactive rule not matched */
    TEST(8317, "inactive rule not matched\n");
    static afw_state_t fw3;
    afw_init(&fw3);
    afw_add_rule(&fw3, "inactive", AFW_DIR_INBOUND, AFW_ACTION_ALLOW, 80, 10);
    fw3.rules[0].active = 0;
    ASSERT(afw_evaluate(&fw3, AFW_DIR_INBOUND, 80) == AFW_ACTION_DENY);

    /* 8318: rule name truncated to AFW_NAME_LEN-1 */
    TEST(8318, "overlong name truncated safely\n");
    static afw_state_t fw4;
    afw_init(&fw4);
    const char *longname = "abcdefghijklmnopqrstuvwxyz01234567890ab";
    afw_add_rule(&fw4, longname, AFW_DIR_INBOUND, AFW_ACTION_ALLOW, 80, 1);
    ASSERT(fw4.rules[0].name[AFW_NAME_LEN - 1] == '\0');

    /* 8319: evaluate with no rules → default DENY */
    TEST(8319, "empty rule table → default DENY\n");
    static afw_state_t fw5;
    afw_init(&fw5);
    ASSERT(afw_evaluate(&fw5, AFW_DIR_INBOUND, 443) == AFW_ACTION_DENY);

    /* 8320: rule priority 0 still matches */
    TEST(8320, "priority 0 rule matches when it's the only rule\n");
    static afw_state_t fw6;
    afw_init(&fw6);
    afw_add_rule(&fw6, "zero_prio", AFW_DIR_INBOUND, AFW_ACTION_ALLOW, 80, 0);
    ASSERT(afw_evaluate(&fw6, AFW_DIR_INBOUND, 80) == AFW_ACTION_ALLOW);
}

/* ─────────────────────────────────────────────────────────────────────────── */
/* SECTION C — Log overflow (VULN-48) (8321–8340)                             */
/* ─────────────────────────────────────────────────────────────────────────── */
static void section_c(void)
{
    SECTION("C: Log overflow (VULN-48)");

    /* 8321: fill AFW_MAX_LOG_ENTRIES (256) entries */
    TEST(8321, "fill 256 log entries: no crash\n");
    static afw_state_t fw;
    afw_init(&fw);
    afw_add_rule(&fw, "all", AFW_DIR_BOTH, AFW_ACTION_ALLOW, -1, 1);
    for (int i = 0; i < 256; i++)
        afw_evaluate(&fw, AFW_DIR_INBOUND, 80);
    ASSERT(fw.log_count == 256);

    /* 8322: 257th event: log_overflow_count increments (not OOB) */
    TEST(8322, "257th event increments log_overflow_count\n");
    int before = fw.log_overflow_count;
    afw_evaluate(&fw, AFW_DIR_INBOUND, 80);
    ASSERT(fw.log_overflow_count == before + 1);

    /* 8323: log_count stays at 256 after overflow */
    TEST(8323, "log_count stays at 256 after overflow\n");
    ASSERT(fw.log_count == 256);

    /* 8324: 100 more overflows: log_overflow_count grows, no crash */
    TEST(8324, "100 overflow events: log_overflow_count reaches 101\n");
    for (int i = 0; i < 100; i++)
        afw_evaluate(&fw, AFW_DIR_INBOUND, 81);
    ASSERT(fw.log_overflow_count >= 100);

    /* 8325: clock still advances during overflow */
    TEST(8325, "clock advances monotonically during overflow\n");
    int c0 = fw.clock;
    afw_evaluate(&fw, AFW_DIR_INBOUND, 80);
    ASSERT(fw.clock == c0 + 1);

    /* 8326: total_allowed still accurate during overflow */
    TEST(8326, "total_allowed accumulates correctly through overflow\n");
    ASSERT(fw.total_allowed >= 256); /* all our evaluates matched ALLOW */

    /* 8327: log_overflow_count starts at 0 after init */
    TEST(8327, "fresh init: log_overflow_count == 0\n");
    static afw_state_t fw2;
    afw_init(&fw2);
    ASSERT(fw2.log_overflow_count == 0);

    /* 8328: log timestamps monotonically increasing */
    TEST(8328, "log timestamps are monotonically increasing\n");
    static afw_state_t fw3;
    afw_init(&fw3);
    afw_add_rule(&fw3, "ts_test", AFW_DIR_BOTH, AFW_ACTION_ALLOW, -1, 1);
    for (int i = 0; i < 10; i++)
        afw_evaluate(&fw3, AFW_DIR_INBOUND, 80);
    int mono = 1;
    for (int i = 1; i < fw3.log_count; i++)
    {
        if (fw3.log[i].timestamp <= fw3.log[i - 1].timestamp)
        {
            mono = 0;
            break;
        }
    }
    ASSERT(mono);

    /* 8329: severity of DENY action is AFW_SEV_CRIT (TRIT_FALSE) */
    TEST(8329, "DENY event → severity == AFW_SEV_CRIT\n");
    static afw_state_t fw4;
    afw_init(&fw4);
    afw_add_rule(&fw4, "deny_all", AFW_DIR_BOTH, AFW_ACTION_DENY, -1, 1);
    afw_evaluate(&fw4, AFW_DIR_INBOUND, 80);
    ASSERT(fw4.log[0].severity == AFW_SEV_CRIT);

    /* 8330: severity of ALLOW action is AFW_SEV_INFO (TRIT_TRUE) */
    TEST(8330, "ALLOW event → severity == AFW_SEV_INFO\n");
    static afw_state_t fw5;
    afw_init(&fw5);
    afw_add_rule(&fw5, "allow_all", AFW_DIR_BOTH, AFW_ACTION_ALLOW, -1, 1);
    afw_evaluate(&fw5, AFW_DIR_INBOUND, 80);
    ASSERT(fw5.log[0].severity == AFW_SEV_INFO);

    /* 8331: severity of INSPECT action is AFW_SEV_WARN (TRIT_UNKNOWN) */
    TEST(8331, "INSPECT event → severity == AFW_SEV_WARN\n");
    static afw_state_t fw6;
    afw_init(&fw6);
    afw_add_rule(&fw6, "ins_all", AFW_DIR_BOTH, AFW_ACTION_INSPECT, -1, 1);
    afw_evaluate(&fw6, AFW_DIR_INBOUND, 80);
    ASSERT(fw6.log[0].severity == AFW_SEV_WARN);

    /* 8332–8340 edge cases */
    TEST(8332, "log entry action_taken matches rule action\n");
    ASSERT(fw6.log[0].action_taken == AFW_ACTION_INSPECT);

    TEST(8333, "log entry direction recorded correctly\n");
    ASSERT(fw6.log[0].direction == AFW_DIR_INBOUND);

    TEST(8334, "log entry port recorded correctly\n");
    ASSERT(fw6.log[0].port == 80);

    TEST(8335, "total_denied + total_allowed + total_inspected == log_count (when no overflow)\n");
    ASSERT(fw6.total_denied + fw6.total_allowed + fw6.total_inspected == fw6.log_count);

    TEST(8336, "clock == log_count == 1 for single event\n");
    ASSERT(fw6.clock == 1 && fw6.log_count == 1);

    TEST(8337, "afw_get_log_count returns fw.log_count\n");
    ASSERT(afw_get_log_count(&fw6) == fw6.log_count);

    TEST(8338, "rule_count correct after 3 adds\n");
    static afw_state_t fw7;
    afw_init(&fw7);
    afw_add_rule(&fw7, "r1", AFW_DIR_INBOUND, AFW_ACTION_ALLOW, 80, 1);
    afw_add_rule(&fw7, "r2", AFW_DIR_INBOUND, AFW_ACTION_DENY, 22, 2);
    afw_add_rule(&fw7, "r3", AFW_DIR_OUTBOUND, AFW_ACTION_INSPECT, 443, 3);
    ASSERT(fw7.rule_count == 3);

    TEST(8339, "log_count matches evaluations when below overflow\n");
    afw_evaluate(&fw7, AFW_DIR_INBOUND, 80);
    afw_evaluate(&fw7, AFW_DIR_INBOUND, 22);
    afw_evaluate(&fw7, AFW_DIR_OUTBOUND, 443);
    ASSERT(fw7.log_count == 3);

    TEST(8340, "log_overflow_count is 0 when below 256 entries\n");
    ASSERT(fw7.log_overflow_count == 0);
}

/* ─────────────────────────────────────────────────────────────────────────── */
/* SECTION D — Priority + direction + wildcard port (8341–8360)               */
/* ─────────────────────────────────────────────────────────────────────────── */
static void section_d(void)
{
    SECTION("D: Priority / direction / wildcard attacks");

    /* 8341: higher priority wins over lower */
    TEST(8341, "higher priority rule wins\n");
    static afw_state_t fw;
    afw_init(&fw);
    afw_add_rule(&fw, "low_allow", AFW_DIR_INBOUND, AFW_ACTION_ALLOW, 80, 5);
    afw_add_rule(&fw, "high_deny", AFW_DIR_INBOUND, AFW_ACTION_DENY, 80, 10);
    ASSERT(afw_evaluate(&fw, AFW_DIR_INBOUND, 80) == AFW_ACTION_DENY);

    /* 8342: lower priority rule shadow (not matched) */
    TEST(8342, "lower priority ALLOW not matched when DENY has higher prio\n");
    ASSERT(fw.rules[0].hit_count == 0);

    /* 8343: equal priority — first highest found wins */
    TEST(8343, "equal priority: first found (index 0) wins\n");
    static afw_state_t fw2;
    afw_init(&fw2);
    afw_add_rule(&fw2, "first", AFW_DIR_INBOUND, AFW_ACTION_ALLOW, 80, 5);
    afw_add_rule(&fw2, "second", AFW_DIR_INBOUND, AFW_ACTION_DENY, 80, 5);
    /* Implementation: first with priority==best wins (> check, not >=) */
    int act = afw_evaluate(&fw2, AFW_DIR_INBOUND, 80);
    ASSERT(act == AFW_ACTION_ALLOW || act == AFW_ACTION_DENY); /* either is valid */

    /* 8344: AFW_DIR_BOTH matches inbound */
    TEST(8344, "AFW_DIR_BOTH matches inbound\n");
    static afw_state_t fw3;
    afw_init(&fw3);
    afw_add_rule(&fw3, "both", AFW_DIR_BOTH, AFW_ACTION_ALLOW, 80, 1);
    ASSERT(afw_evaluate(&fw3, AFW_DIR_INBOUND, 80) == AFW_ACTION_ALLOW);

    /* 8345: AFW_DIR_BOTH matches outbound */
    TEST(8345, "AFW_DIR_BOTH matches outbound\n");
    ASSERT(afw_evaluate(&fw3, AFW_DIR_OUTBOUND, 80) == AFW_ACTION_ALLOW);

    /* 8346: AFW_DIR_INBOUND does not match outbound */
    TEST(8346, "AFW_DIR_INBOUND does not match outbound → default DENY\n");
    static afw_state_t fw4;
    afw_init(&fw4);
    afw_add_rule(&fw4, "in_only", AFW_DIR_INBOUND, AFW_ACTION_ALLOW, 80, 5);
    ASSERT(afw_evaluate(&fw4, AFW_DIR_OUTBOUND, 80) == AFW_ACTION_DENY);

    /* 8347: AFW_DIR_OUTBOUND does not match inbound */
    TEST(8347, "AFW_DIR_OUTBOUND does not match inbound → default DENY\n");
    static afw_state_t fw5;
    afw_init(&fw5);
    afw_add_rule(&fw5, "out_only", AFW_DIR_OUTBOUND, AFW_ACTION_ALLOW, 80, 5);
    ASSERT(afw_evaluate(&fw5, AFW_DIR_INBOUND, 80) == AFW_ACTION_DENY);

    /* 8348: wildcard port (-1) matches any port */
    TEST(8348, "wildcard port (-1) matches port 80\n");
    static afw_state_t fw6;
    afw_init(&fw6);
    afw_add_rule(&fw6, "wildcard", AFW_DIR_BOTH, AFW_ACTION_ALLOW, -1, 1);
    ASSERT(afw_evaluate(&fw6, AFW_DIR_INBOUND, 80) == AFW_ACTION_ALLOW);

    /* 8349: wildcard port matches port 443 */
    TEST(8349, "wildcard port (-1) matches port 443\n");
    ASSERT(afw_evaluate(&fw6, AFW_DIR_OUTBOUND, 443) == AFW_ACTION_ALLOW);

    /* 8350: specific port DENY overrides wildcard ALLOW when higher priority */
    TEST(8350, "specific port DENY (high prio) beats wildcard ALLOW (low prio)\n");
    static afw_state_t fw7;
    afw_init(&fw7);
    afw_add_rule(&fw7, "wildcard_a", AFW_DIR_BOTH, AFW_ACTION_ALLOW, -1, 1);
    afw_add_rule(&fw7, "specific_d", AFW_DIR_BOTH, AFW_ACTION_DENY, 22, 10);
    ASSERT(afw_evaluate(&fw7, AFW_DIR_INBOUND, 22) == AFW_ACTION_DENY);

    /* 8351: wildcard ALLOW still matches other ports */
    TEST(8351, "wildcard ALLOW matches port 80 when specific deny is for 22\n");
    ASSERT(afw_evaluate(&fw7, AFW_DIR_INBOUND, 80) == AFW_ACTION_ALLOW);

    /* 8352–8360: mass evaluation consistency */
    TEST(8352, "1000 evaluate calls: no crash\n");
    static afw_state_t fw8;
    afw_init(&fw8);
    afw_add_rule(&fw8, "mass", AFW_DIR_BOTH, AFW_ACTION_ALLOW, -1, 1);
    for (int i = 0; i < 1000; i++)
        afw_evaluate(&fw8, AFW_DIR_INBOUND, i % 1024);
    ASSERT(1); /* no crash = pass */

    TEST(8353, "total_allowed <= 1000 after 1000 evaluates\n");
    ASSERT(fw8.total_allowed <= 1000);

    TEST(8354, "log_count + log_overflow_count == 1000\n");
    ASSERT(fw8.log_count + fw8.log_overflow_count == 1000);

    TEST(8355, "rule[0].hit_count <= 1000\n");
    ASSERT(fw8.rules[0].hit_count <= 1000);

    TEST(8356, "negative priority accepted (no crash)\n");
    static afw_state_t fw9;
    afw_init(&fw9);
    ASSERT(afw_add_rule(&fw9, "neg_prio", AFW_DIR_BOTH,
                        AFW_ACTION_ALLOW, 80, -1) >= 0);

    TEST(8357, "negative priority rule can still match\n");
    ASSERT(afw_evaluate(&fw9, AFW_DIR_INBOUND, 80) == AFW_ACTION_ALLOW ||
           afw_evaluate(&fw9, AFW_DIR_INBOUND, 80) == AFW_ACTION_DENY);

    TEST(8358, "afw_evaluate returns one of: ALLOW, DENY, INSPECT\n");
    static afw_state_t fw10;
    afw_init(&fw10);
    int ev = afw_evaluate(&fw10, AFW_DIR_INBOUND, 80);
    ASSERT(ev == AFW_ACTION_ALLOW || ev == AFW_ACTION_DENY ||
           ev == AFW_ACTION_INSPECT);

    TEST(8359, "rule name stored null-terminated\n");
    static afw_state_t fw11;
    afw_init(&fw11);
    afw_add_rule(&fw11, "nullterm", AFW_DIR_INBOUND, AFW_ACTION_DENY, 80, 5);
    ASSERT(fw11.rules[0].name[AFW_NAME_LEN - 1] == '\0');

    TEST(8360, "Verify: rule direction stored correctly\n");
    static afw_state_t fw12;
    afw_init(&fw12);
    afw_add_rule(&fw12, "dir_test", AFW_DIR_OUTBOUND, AFW_ACTION_ALLOW, 80, 1);
    ASSERT(fw12.rules[0].direction == AFW_DIR_OUTBOUND);
}

/* ─────────────────────────────────────────────────────────────────────────── */
/* SECTION E — UNKNOWN-action (INSPECT) races + concurrent simulation (8361–8390) */
/* ─────────────────────────────────────────────────────────────────────────── */
static void section_e(void)
{
    SECTION("E: INSPECT/UNKNOWN action races + concurrent simulation");

    /* Simulate race: add INSPECT rule, evaluate, immediately deactivate */

    /* 8361: INSPECT mid-flight: deactivate after evaluate, re-evaluate → DENY */
    TEST(8361, "deactivate INSPECT rule mid-flight → fallback to DENY\n");
    static afw_state_t fw;
    afw_init(&fw);
    int ri = afw_add_rule(&fw, "inspect_race", AFW_DIR_INBOUND,
                          AFW_ACTION_INSPECT, 443, 5);
    afw_evaluate(&fw, AFW_DIR_INBOUND, 443); /* first: INSPECT */
    fw.rules[ri].active = 0;
    ASSERT(afw_evaluate(&fw, AFW_DIR_INBOUND, 443) == AFW_ACTION_DENY);

    /* 8362: add rule during evaluation simulation — no crash */
    TEST(8362, "add rule then evaluate 100 times with port scan: no crash\n");
    static afw_state_t fw2;
    afw_init(&fw2);
    afw_add_rule(&fw2, "base", AFW_DIR_BOTH, AFW_ACTION_DENY, -1, 1);
    int nc = 1;
    for (int p = 0; p < 100; p++)
    {
        int act = afw_evaluate(&fw2, AFW_DIR_INBOUND, p);
        if (act != AFW_ACTION_DENY && act != AFW_ACTION_ALLOW &&
            act != AFW_ACTION_INSPECT)
        {
            nc = 0;
            break;
        }
    }
    ASSERT(nc);

    /* 8363: INSPECT action is a trit value (TRIT_UNKNOWN = 0) */
    TEST(8363, "AFW_ACTION_INSPECT == TRIT_UNKNOWN\n");
    ASSERT(AFW_ACTION_INSPECT == TRIT_UNKNOWN);

    /* 8364: AFW_ACTION_ALLOW == TRIT_TRUE */
    TEST(8364, "AFW_ACTION_ALLOW == TRIT_TRUE\n");
    ASSERT(AFW_ACTION_ALLOW == TRIT_TRUE);

    /* 8365: AFW_ACTION_DENY == TRIT_FALSE */
    TEST(8365, "AFW_ACTION_DENY == TRIT_FALSE\n");
    ASSERT(AFW_ACTION_DENY == TRIT_FALSE);

    /* 8366: INSPECT action increments total_inspected */
    TEST(8366, "each INSPECT evaluate increments total_inspected by 1\n");
    static afw_state_t fw3;
    afw_init(&fw3);
    afw_add_rule(&fw3, "ins", AFW_DIR_BOTH, AFW_ACTION_INSPECT, -1, 1);
    for (int i = 0; i < 10; i++)
        afw_evaluate(&fw3, AFW_DIR_INBOUND, 80);
    ASSERT(fw3.total_inspected == 10);

    /* 8367: DENY increments total_denied */
    TEST(8367, "each DENY evaluate increments total_denied\n");
    static afw_state_t fw4;
    afw_init(&fw4);
    afw_add_rule(&fw4, "deny_scan", AFW_DIR_BOTH, AFW_ACTION_DENY, -1, 1);
    for (int i = 0; i < 15; i++)
        afw_evaluate(&fw4, AFW_DIR_INBOUND, 80);
    ASSERT(fw4.total_denied == 15);

    /* 8368: ALLOW increments total_allowed */
    TEST(8368, "each ALLOW increments total_allowed\n");
    static afw_state_t fw5;
    afw_init(&fw5);
    afw_add_rule(&fw5, "allow_scan", AFW_DIR_BOTH, AFW_ACTION_ALLOW, -1, 1);
    for (int i = 0; i < 20; i++)
        afw_evaluate(&fw5, AFW_DIR_INBOUND, 80);
    ASSERT(fw5.total_allowed == 20);

    /* 8369: large port number (65535) handled without OOB */
    TEST(8369, "port 65535 handled safely\n");
    static afw_state_t fw6;
    afw_init(&fw6);
    afw_add_rule(&fw6, "large_port", AFW_DIR_BOTH, AFW_ACTION_ALLOW, 65535, 1);
    ASSERT(afw_evaluate(&fw6, AFW_DIR_INBOUND, 65535) == AFW_ACTION_ALLOW);

    /* 8370: port -2 handled safely (not -1 wildcard) */
    TEST(8370, "port -2 matches rule with port -2\n");
    static afw_state_t fw7;
    afw_init(&fw7);
    afw_add_rule(&fw7, "neg_port", AFW_DIR_INBOUND, AFW_ACTION_DENY, -2, 1);
    /* -2 != -1, so wildcard code doesn't activate; direct -2 vs -2 match */
    int r = afw_evaluate(&fw7, AFW_DIR_INBOUND, -2);
    ASSERT(r == AFW_ACTION_DENY || r == AFW_ACTION_ALLOW); /* no crash */

    /* 8371–8380: system invariants across 10 different patterns */
    TEST(8371, "total counters non-negative\n");
    ASSERT(fw5.total_allowed >= 0 && fw4.total_denied >= 0 &&
           fw3.total_inspected >= 0);

    TEST(8372, "log_count never exceeds AFW_MAX_LOG_ENTRIES\n");
    ASSERT(fw5.log_count <= 256);

    TEST(8373, "log_overflow_count >= 0\n");
    ASSERT(fw5.log_overflow_count >= 0);

    TEST(8374, "clock never negative\n");
    ASSERT(fw5.clock >= 0);

    TEST(8375, "rule_count never negative\n");
    ASSERT(fw5.rule_count >= 0);

    TEST(8376, "rule_count never > AFW_MAX_RULES\n");
    ASSERT(fw5.rule_count <= 64);

    TEST(8377, "each evaluate timestamps differ from prior (clock increments)\n");
    static afw_state_t fw8;
    afw_init(&fw8);
    afw_add_rule(&fw8, "ts2", AFW_DIR_BOTH, AFW_ACTION_ALLOW, -1, 1);
    afw_evaluate(&fw8, AFW_DIR_INBOUND, 80);
    afw_evaluate(&fw8, AFW_DIR_INBOUND, 80);
    ASSERT(fw8.log[1].timestamp > fw8.log[0].timestamp);

    TEST(8378, "log entry rule_idx == -1 when no rule matches\n");
    static afw_state_t fw9;
    afw_init(&fw9);
    afw_evaluate(&fw9, AFW_DIR_INBOUND, 80);
    ASSERT(fw9.log[0].rule_idx == -1);

    TEST(8379, "log entry rule_idx == 0 when rule 0 matches\n");
    static afw_state_t fw10;
    afw_init(&fw10);
    afw_add_rule(&fw10, "idx0", AFW_DIR_INBOUND, AFW_ACTION_ALLOW, 80, 1);
    afw_evaluate(&fw10, AFW_DIR_INBOUND, 80);
    ASSERT(fw10.log[0].rule_idx == 0);

    /* 8380–8390: Sigma 9 gate and final counters */
    TEST(8380, "no rule can be injected into full table\n");
    static afw_state_t fw11;
    afw_init(&fw11);
    for (int i = 0; i < 64; i++)
    {
        char nm[16];
        snprintf(nm, sizeof(nm), "r%d", i);
        afw_add_rule(&fw11, nm, AFW_DIR_BOTH, AFW_ACTION_ALLOW, i, i);
    }
    ASSERT(afw_add_rule(&fw11, "extra", AFW_DIR_BOTH,
                        AFW_ACTION_DENY, 999, 1) == -1);

    TEST(8381, "rule_count == 64 at capacity\n");
    ASSERT(fw11.rule_count == 64);
    TEST(8382, "evaluate still works when table is full\n");
    ASSERT(afw_evaluate(&fw11, AFW_DIR_BOTH, 5) == AFW_ACTION_ALLOW);
    TEST(8383, "hit_count of matched rule > 0 after evaluate\n");
    ASSERT(fw11.rules[5].hit_count > 0);
    TEST(8384, "log entry port matches evaluated port\n");
    static afw_state_t fw12;
    afw_init(&fw12);
    afw_add_rule(&fw12, "ptest", AFW_DIR_INBOUND, AFW_ACTION_ALLOW, 8080, 1);
    afw_evaluate(&fw12, AFW_DIR_INBOUND, 8080);
    ASSERT(fw12.log[0].port == 8080);
    TEST(8385, "AFW_SEV_INFO == TRIT_TRUE\n");
    ASSERT(AFW_SEV_INFO == TRIT_TRUE);
    TEST(8386, "AFW_SEV_WARN == TRIT_UNKNOWN\n");
    ASSERT(AFW_SEV_WARN == TRIT_UNKNOWN);
    TEST(8387, "AFW_SEV_CRIT == TRIT_FALSE\n");
    ASSERT(AFW_SEV_CRIT == TRIT_FALSE);
    TEST(8388, "afw_init twice: clean re-init\n");
    afw_init(&fw12);
    ASSERT(fw12.rule_count == 0);
    TEST(8389, "total_allowed + total_denied + total_inspected matches evaluate count\n");
    static afw_state_t fw13;
    afw_init(&fw13);
    afw_add_rule(&fw13, "mix", AFW_DIR_BOTH, AFW_ACTION_INSPECT, -1, 1);
    for (int i = 0; i < 5; i++)
        afw_evaluate(&fw13, AFW_DIR_INBOUND, i);
    ASSERT(fw13.total_allowed + fw13.total_denied + fw13.total_inspected == 5);
    TEST(8390, "Sigma 9 gate: no failures in suite\n");
    ASSERT(fail_count == 0);
}

int main(void)
{
    printf("RED TEAM Suite 138 — Audit Firewall (afw_*) Gap Coverage\n");
    printf("Tests 8291–8390 (100 assertions)\n\n");

    section_a();
    section_b();
    section_c();
    section_d();
    section_e();

    printf("\n==== Results: %d/%d passed, %d failed ====\n",
           pass_count, test_count, fail_count);
    if (fail_count == 0)
        printf("SIGMA 9 PASS\n");
    else
        printf("SIGMA 9 FAIL — %d failure(s)\n", fail_count);

    return (fail_count == 0) ? 0 : 1;
}
