/**
 * @file test_hardening.c
 * @brief seT6 — Attack Surface Reduction & Hardening Test Suite
 *
 * Tests the Arch Linux–inspired hardening framework:
 *   - Kernel parameter emulation (kptr_restrict, etc.)
 *   - Restrictive mount options (noexec, nodev, nosuid)
 *   - Ternary firewall rules and packet filtering
 *   - SUID audit and vulnerability scanning
 *   - Hardening score computation
 *
 * Target: 50+ assertions.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "set6/trit.h"
#include "trit_hardening.h"

/* ======================================================================== */
/*  Test Harness                                                            */
/* ======================================================================== */

static int tests_passed = 0;
static int tests_failed = 0;
static int tests_total  = 0;

#define TEST(name) do { \
    tests_total++; \
    printf("  %-60s", name); \
} while(0)

#define PASS() do { \
    tests_passed++; \
    printf("[PASS]\n"); \
} while(0)

#define FAIL(msg) do { \
    tests_failed++; \
    printf("[FAIL] %s\n", msg); \
} while(0)

#define ASSERT(cond, msg) do { \
    if (cond) { PASS(); } else { FAIL(msg); } \
} while(0)

#define SECTION(name) printf("\n  --- %s ---\n", name)

/* ======================================================================== */
/*  Test: Initialization                                                    */
/* ======================================================================== */

static void test_init(void) {
    SECTION("Hardening Initialization");

    thard_state_t hs;

    TEST("Init returns OK");
    ASSERT(thard_init(&hs) == THARD_OK, "init failed");

    TEST("Hardening status is UNKNOWN (partial)");
    ASSERT(hs.hardening_status == TRIT_UNKNOWN, "expected UNKNOWN");

    TEST("Param count starts at 0");
    ASSERT(hs.param_count == 0, "expected 0");

    TEST("Mount count starts at 0");
    ASSERT(hs.mount_count == 0, "expected 0");

    TEST("Init with NULL");
    ASSERT(thard_init(NULL) == THARD_ERR_INIT, "expected ERR_INIT");
}

/* ======================================================================== */
/*  Test: Kernel Parameter Emulation                                        */
/* ======================================================================== */

static void test_kparams(void) {
    SECTION("Kernel Parameter Emulation");

    thard_state_t hs;
    thard_init(&hs);

    TEST("Set kptr_restrict=2");
    ASSERT(thard_set_kparam(&hs, TKPARAM_KPTR_RESTRICT, 2) == THARD_OK,
           "set failed");

    TEST("Get kptr_restrict value");
    ASSERT(thard_get_kparam(&hs, TKPARAM_KPTR_RESTRICT) == 2, "expected 2");

    TEST("Set dmesg_restrict=1");
    ASSERT(thard_set_kparam(&hs, TKPARAM_DMESG_RESTRICT, 1) == THARD_OK,
           "set failed");

    TEST("Set perf_restrict=3");
    ASSERT(thard_set_kparam(&hs, TKPARAM_PERF_RESTRICT, 3) == THARD_OK,
           "set failed");

    TEST("Set mmap_min_addr=65536");
    ASSERT(thard_set_kparam(&hs, TKPARAM_MMAP_MIN_ADDR, 65536) == THARD_OK,
           "set failed");

    TEST("Set randomize_va=2 (full ASLR)");
    ASSERT(thard_set_kparam(&hs, TKPARAM_RANDOMIZE_VA, 2) == THARD_OK,
           "set failed");

    TEST("Set stack_protect=1");
    ASSERT(thard_set_kparam(&hs, TKPARAM_STACK_PROTECT, 1) == THARD_OK,
           "set failed");

    TEST("Param count is 6");
    ASSERT(hs.param_count == 6, "expected 6");

    TEST("Override kptr_restrict to 1");
    ASSERT(thard_set_kparam(&hs, TKPARAM_KPTR_RESTRICT, 1) == THARD_OK,
           "override failed");

    TEST("Verify override applied");
    ASSERT(thard_get_kparam(&hs, TKPARAM_KPTR_RESTRICT) == 1, "expected 1");

    TEST("Get non-existent param");
    ASSERT(thard_get_kparam(&hs, 99) == -1, "expected -1");
}

/* ======================================================================== */
/*  Test: Restrictive Mounts                                                */
/* ======================================================================== */

static void test_mounts(void) {
    SECTION("Restrictive Mount Options");

    thard_state_t hs;
    thard_init(&hs);

    TEST("Add /tmp with noexec|nosuid|nodev");
    ASSERT(thard_mount_add(&hs, "/tmp", TMOUNT_NOEXEC | TMOUNT_NOSUID | TMOUNT_NODEV) == THARD_OK,
           "add failed");

    TEST("Add /var/run with noexec");
    ASSERT(thard_mount_add(&hs, "/var/run", TMOUNT_NOEXEC) == THARD_OK,
           "add failed");

    TEST("Add /sys with readonly");
    ASSERT(thard_mount_add(&hs, "/sys", TMOUNT_READONLY) == THARD_OK,
           "add failed");

    TEST("Mount count is 3");
    ASSERT(hs.mount_count == 3, "expected 3");

    TEST("Check /tmp exec attempt — DENIED");
    ASSERT(thard_mount_check(&hs, "/tmp", TMOUNT_NOEXEC) == THARD_ERR_DENIED,
           "expected DENIED");

    TEST("Check /tmp suid attempt — DENIED");
    ASSERT(thard_mount_check(&hs, "/tmp", TMOUNT_NOSUID) == THARD_ERR_DENIED,
           "expected DENIED");

    TEST("Check /tmp dev attempt — DENIED");
    ASSERT(thard_mount_check(&hs, "/tmp", TMOUNT_NODEV) == THARD_ERR_DENIED,
           "expected DENIED");

    TEST("Check /sys write attempt — DENIED");
    ASSERT(thard_mount_check(&hs, "/sys", TMOUNT_READONLY) == THARD_ERR_DENIED,
           "expected DENIED");

    TEST("Check /var/run suid (not restricted) — OK");
    ASSERT(thard_mount_check(&hs, "/var/run", TMOUNT_NOSUID) == THARD_OK,
           "expected OK");

    TEST("Check unknown mount — NOTFOUND");
    ASSERT(thard_mount_check(&hs, "/unknown", TMOUNT_NOEXEC) == THARD_ERR_NOTFOUND,
           "expected NOTFOUND");

    TEST("Violations count on /tmp is 3");
    ASSERT(hs.mounts[0].violations == 3, "expected 3 violations");
}

/* ======================================================================== */
/*  Test: Ternary Firewall                                                  */
/* ======================================================================== */

static void test_firewall(void) {
    SECTION("Ternary Firewall");

    thard_state_t hs;
    thard_init(&hs);

    TEST("Add ACCEPT rule for module 0→1");
    ASSERT(thard_fw_add_rule(&hs, "allow_0_1", TFW_DIR_OUTBOUND,
           TFW_ACTION_ACCEPT, 0, 1) == THARD_OK, "add failed");

    TEST("Add DROP rule for module 5→* (any dest)");
    ASSERT(thard_fw_add_rule(&hs, "block_mod5", TFW_DIR_BOTH,
           TFW_ACTION_DROP, 5, -1) == THARD_OK, "add failed");

    TEST("Add LOG rule for module *→3 (any source)");
    ASSERT(thard_fw_add_rule(&hs, "log_to_3", TFW_DIR_INBOUND,
           TFW_ACTION_LOG, -1, 3) == THARD_OK, "add failed");

    TEST("Rule count is 3");
    ASSERT(hs.fw_rule_count == 3, "expected 3");

    TEST("Check 0→1 outbound — ACCEPT");
    ASSERT(thard_fw_check(&hs, 0, 1, TFW_DIR_OUTBOUND) == TFW_ACTION_ACCEPT,
           "expected ACCEPT");

    TEST("Check 5→2 outbound — DROP");
    ASSERT(thard_fw_check(&hs, 5, 2, TFW_DIR_OUTBOUND) == TFW_ACTION_DROP,
           "expected DROP");

    TEST("Check X→3 inbound — LOG");
    ASSERT(thard_fw_check(&hs, 99, 3, TFW_DIR_INBOUND) == TFW_ACTION_LOG,
           "expected LOG");

    TEST("Check 1→2 (no rule) — default ACCEPT");
    ASSERT(thard_fw_check(&hs, 1, 2, TFW_DIR_OUTBOUND) == TRIT_TRUE,
           "expected default ACCEPT");

    TEST("Dropped packets count");
    ASSERT(thard_fw_dropped(&hs) == 1, "expected 1 dropped");

    TEST("Accepted packets count");
    ASSERT(hs.fw_packets_accepted == 2, "expected 2 accepted");

    TEST("Logged packets count");
    ASSERT(hs.fw_packets_logged == 1, "expected 1 logged");
}

/* ======================================================================== */
/*  Test: SUID Audit                                                        */
/* ======================================================================== */

static void test_audit(void) {
    SECTION("SUID Audit & Vulnerability Scan");

    thard_state_t hs;
    thard_init(&hs);

    TEST("Audit module 0 — no SUID");
    ASSERT(thard_audit_module(&hs, 0, 0) == THARD_OK, "audit failed");

    TEST("Module 0 status is TRUE (clean)");
    ASSERT(hs.audit[0].status == TRIT_TRUE, "expected clean");

    TEST("Audit module 1 — has SUID");
    ASSERT(thard_audit_module(&hs, 1, 1) == THARD_OK, "audit failed");

    TEST("Module 1 status is FALSE (vulnerable)");
    ASSERT(hs.audit[1].status == TRIT_FALSE, "expected vulnerable");

    TEST("Module 1 severity is CRIT");
    ASSERT(hs.audit[1].severity == TAUDIT_SEV_CRIT, "expected CRIT");

    TEST("Audit module 2 — no SUID");
    ASSERT(thard_audit_module(&hs, 2, 0) == THARD_OK, "audit failed");

    TEST("Audit module 3 — has SUID");
    ASSERT(thard_audit_module(&hs, 3, 1) == THARD_OK, "audit failed");

    TEST("SUID found count is 2");
    ASSERT(hs.suid_found == 2, "expected 2");

    TEST("Full audit scan — 2 vulnerabilities");
    ASSERT(thard_audit_scan(&hs) == 2, "expected 2 vulns");

    TEST("Vulnerabilities field updated");
    ASSERT(hs.vulnerabilities == 2, "expected 2");
}

/* ======================================================================== */
/*  Test: Hardening Score                                                   */
/* ======================================================================== */

static void test_score(void) {
    SECTION("Hardening Score Computation");

    thard_state_t hs;
    thard_init(&hs);

    TEST("Score with nothing configured — 0");
    ASSERT(thard_compute_score(&hs) == 0, "expected 0");

    /* Configure hardening features */
    thard_set_kparam(&hs, TKPARAM_KPTR_RESTRICT, 2);
    thard_set_kparam(&hs, TKPARAM_DMESG_RESTRICT, 1);
    thard_set_kparam(&hs, TKPARAM_RANDOMIZE_VA, 2);

    TEST("Score with 3 kparams — 30");
    int score = thard_compute_score(&hs);
    ASSERT(score == 30, "expected 30");

    thard_mount_add(&hs, "/tmp", TMOUNT_NOEXEC | TMOUNT_NOSUID);
    thard_mount_add(&hs, "/sys", TMOUNT_READONLY);

    TEST("Score with 3 kparams + 2 mounts — 40");
    score = thard_compute_score(&hs);
    ASSERT(score == 40, "expected 40");

    thard_fw_add_rule(&hs, "r1", TFW_DIR_BOTH, TFW_ACTION_DROP, -1, -1);
    thard_fw_add_rule(&hs, "r2", TFW_DIR_INBOUND, TFW_ACTION_ACCEPT, 0, 1);

    TEST("Score with kparams+mounts+fw — 46");
    score = thard_compute_score(&hs);
    ASSERT(score == 46, "expected 46");

    /* Clean audit (no SUID) */
    thard_audit_module(&hs, 0, 0);
    thard_audit_module(&hs, 1, 0);

    TEST("Score with clean audit bonus — 66");
    score = thard_compute_score(&hs);
    ASSERT(score == 66, "expected 66");

    /* Maximise hardening for full-coverage test */
    thard_set_kparam(&hs, TKPARAM_PERF_RESTRICT, 3);
    thard_set_kparam(&hs, TKPARAM_MMAP_MIN_ADDR, 65536);
    thard_set_kparam(&hs, TKPARAM_STACK_PROTECT, 1);
    thard_mount_add(&hs, "/var/tmp", TMOUNT_NOEXEC | TMOUNT_NOSUID | TMOUNT_NODEV);
    thard_mount_add(&hs, "/dev/shm", TMOUNT_NOEXEC | TMOUNT_NOSUID);
    thard_mount_add(&hs, "/boot",    TMOUNT_READONLY);
    thard_mount_add(&hs, "/home",    TMOUNT_NOSUID | TMOUNT_NODEV);
    thard_fw_add_rule(&hs, "r3", TFW_DIR_OUTBOUND, TFW_ACTION_DROP, 2, -1);
    thard_fw_add_rule(&hs, "r4", TFW_DIR_INBOUND,  TFW_ACTION_LOG,  -1, 3);
    thard_fw_add_rule(&hs, "r5", TFW_DIR_BOTH,     TFW_ACTION_DROP, 4, 5);
    thard_fw_add_rule(&hs, "r6", TFW_DIR_OUTBOUND, TFW_ACTION_ACCEPT, 0, -1);
    thard_fw_add_rule(&hs, "r7", TFW_DIR_INBOUND,  TFW_ACTION_ACCEPT, -1, 0);

    TEST("Score fully hardened — 131");
    score = thard_compute_score(&hs);
    ASSERT(score == 131, "expected 131");

    TEST("Hardening status is TRUE (fully hardened)");
    ASSERT(hs.hardening_status == TRIT_TRUE, "expected TRUE");
}

/* ======================================================================== */
/*  Main                                                                    */
/* ======================================================================== */

int main(void) {
    printf("\n╔══════════════════════════════════════════════════════════════╗\n");
    printf("║  seT6 Attack Surface Reduction & Hardening Test Suite       ║\n");
    printf("╚══════════════════════════════════════════════════════════════╝\n");

    test_init();
    test_kparams();
    test_mounts();
    test_firewall();
    test_audit();
    test_score();

    printf("\n══════════════════════════════════════════════════════════════\n");
    printf("  Hardening Tests: %d passed, %d failed, %d total\n",
           tests_passed, tests_failed, tests_total);
    printf("══════════════════════════════════════════════════════════════\n");

    return tests_failed > 0 ? 1 : 0;
}
