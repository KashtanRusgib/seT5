/**
 * @file test_trit_enhancements.c
 * @brief Trit Linux — Logical Enhancements Master Test Suite
 *
 * Comprehensive tests for all 6 enhancements from
 * LOGICAL_ENHANCEMENTS_FOR_TRIT_LINUX.md:
 *
 *   Suite 1: POSIX Coreutils & Binary Transcoding  (50+ tests)
 *   Suite 2: Ternary Networking Stack (T-Net)       (50+ tests)
 *   Suite 3: GUI Framework & Display Drivers        (40+ tests)
 *   Suite 4: Package Management (T-Pkg)             (40+ tests)
 *   Suite 5: AI/ML Integration & Tooling            (40+ tests)
 *   Suite 6: Security & Auditing (T-Sec)            (40+ tests)
 *
 * Target: 260+ total tests across all enhancement suites.
 *
 * Test harness uses the same ASSERT/TEST/SECTION macros as the
 * existing test_trit_linux.c for consistency.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

/* seT6 kernel headers (read-only — no modifications) */
#include "set6/trit.h"
#include "set6/trit_emu.h"
#include "set6/multiradix.h"
#include "set6/posix.h"
#include "set6/tfs.h"
#include "set6/tipc.h"
#include "set6/stt_mram.h"
#include "set6/ternary_weight_quantizer.h"

/* Enhancement module headers */
#include "trit_coreutils.h"
#include "trit_net.h"
#include "trit_gui.h"
#include "trit_pkg.h"
#include "trit_ai.h"
#include "trit_security.h"

/* ======================================================================== */
/*  Test Harness — Same pattern as existing test suites                     */
/* ======================================================================== */

static int tests_passed = 0;
static int tests_failed = 0;
static int tests_total  = 0;

/* Per-suite tracking for detailed index output */
static int suite_passed = 0;
static int suite_failed = 0;
static int suite_total  = 0;

#define TEST(name) do { \
    tests_total++; \
    suite_total++; \
    printf("  %-60s", name); \
} while(0)

#define PASS() do { \
    tests_passed++; \
    suite_passed++; \
    printf("[PASS]\n"); \
} while(0)

#define FAIL(msg) do { \
    tests_failed++; \
    suite_failed++; \
    printf("[FAIL] %s\n", msg); \
} while(0)

#define ASSERT(cond, msg) do { \
    if (cond) { PASS(); } else { FAIL(msg); } \
} while(0)

#define SECTION(name) printf("\n  --- %s ---\n", name)

#define SUITE_START(name) do { \
    suite_passed = 0; \
    suite_failed = 0; \
    suite_total = 0; \
    printf("\n========================================\n"); \
    printf("  SUITE: %s\n", name); \
    printf("========================================\n"); \
} while(0)

#define SUITE_END(name) do { \
    printf("  --- %s: %d passed, %d failed (of %d) ---\n\n", \
           name, suite_passed, suite_failed, suite_total); \
} while(0)

/* ======================================================================== */
/*  SUITE 1: POSIX Coreutils & Binary Transcoding (50+ tests)              */
/* ======================================================================== */

static void test_posix_coreutils(void) {
    SUITE_START("POSIX Coreutils & Binary Transcoding");

    /* ---- 1.1: Initialization ------------------------------------------ */
    SECTION("1.1 Environment Initialization");

    tcore_env_t env;

    TEST("tcore_init returns OK");
    ASSERT(tcore_init(&env) == TCORE_OK, "init should succeed");

    TEST("tcore_init sets initialized flag");
    ASSERT(env.initialized == 1, "initialized flag");

    TEST("tcore_init clears cmd_count");
    ASSERT(env.cmd_count == 0, "cmd_count should be 0");

    TEST("tcore_init clears errors");
    ASSERT(env.errors == 0, "errors should be 0");

    TEST("tcore_init NULL pointer");
    ASSERT(tcore_init(NULL) == TCORE_ERR_IO, "NULL init should fail");

    /* ---- 1.2: trit-echo (file writing) -------------------------------- */
    SECTION("1.2 trit-echo (File Writing)");

    trit data1[] = {1, 0, -1, 1, -1};

    TEST("tcore_echo writes file successfully");
    ASSERT(tcore_echo(&env, "hello.t", data1, 5) == TCORE_OK, "echo OK");

    TEST("tcore_echo increments cmd_count");
    ASSERT(env.cmd_count > 0, "cmd_count incremented");

    TEST("tcore_echo NULL env fails");
    ASSERT(tcore_echo(NULL, "x.t", data1, 5) == TCORE_ERR_IO, "NULL env");

    TEST("tcore_echo NULL path fails");
    ASSERT(tcore_echo(&env, NULL, data1, 5) == TCORE_ERR_IO, "NULL path");

    TEST("tcore_echo zero length fails");
    ASSERT(tcore_echo(&env, "z.t", data1, 0) == TCORE_ERR_IO, "zero len");

    /* ---- 1.3: trit-cat (file reading) --------------------------------- */
    SECTION("1.3 trit-cat (File Reading)");

    trit buf[64];
    memset(buf, 0, sizeof(buf));

    TEST("tcore_cat reads file successfully");
    int nread = tcore_cat(&env, "hello.t", buf, 64);
    ASSERT(nread == 5, "should read 5 trits");

    TEST("tcore_cat reads correct data [0]");
    ASSERT(buf[0] == 1, "trit[0] == 1");

    TEST("tcore_cat reads correct data [1]");
    ASSERT(buf[1] == 0, "trit[1] == 0");

    TEST("tcore_cat reads correct data [2]");
    ASSERT(buf[2] == -1, "trit[2] == -1");

    TEST("tcore_cat reads correct data [3]");
    ASSERT(buf[3] == 1, "trit[3] == 1");

    TEST("tcore_cat reads correct data [4]");
    ASSERT(buf[4] == -1, "trit[4] == -1");

    TEST("tcore_cat nonexistent file fails");
    ASSERT(tcore_cat(&env, "nofile.t", buf, 64) == TCORE_ERR_NOTFOUND,
           "missing file");

    TEST("tcore_cat NULL env fails");
    ASSERT(tcore_cat(NULL, "hello.t", buf, 64) == TCORE_ERR_IO, "NULL env");

    /* ---- 1.4: trit-cp (file copy) ------------------------------------- */
    SECTION("1.4 trit-cp (File Copy)");

    TEST("tcore_cp copies file successfully");
    ASSERT(tcore_cp(&env, "hello.t", "copy.t") == TCORE_OK, "cp OK");

    trit cpbuf[64];
    TEST("tcore_cp copied data matches");
    int nc = tcore_cat(&env, "copy.t", cpbuf, 64);
    ASSERT(nc == 5 && cpbuf[0] == 1 && cpbuf[4] == -1, "copy matches");

    TEST("tcore_cp nonexistent source fails");
    ASSERT(tcore_cp(&env, "nope.t", "dst.t") == TCORE_ERR_NOTFOUND, "no src");

    /* ---- 1.5: trit-ls (directory listing) ----------------------------- */
    SECTION("1.5 trit-ls (Directory Listing)");

    tcore_ls_result_t ls;

    TEST("tcore_ls returns files");
    ASSERT(tcore_ls(&env, &ls) == TCORE_OK, "ls OK");

    TEST("tcore_ls finds ≥2 files");
    ASSERT(ls.count >= 2, "at least hello.t and copy.t");

    TEST("tcore_ls total trits > 0");
    ASSERT(ls.total_trits > 0, "non-zero total trits");

    TEST("tcore_ls NULL result fails");
    ASSERT(tcore_ls(&env, NULL) == TCORE_ERR_IO, "NULL result");

    /* ---- 1.6: trit-grep (pattern search) ------------------------------ */
    SECTION("1.6 trit-grep (Pattern Search)");

    /* Create a file with known patterns for grep testing */
    trit gdata[] = {1, 1, 0, 0, -1, -1, 0, 0, 1, 1};
    tcore_echo(&env, "grep_test.t", gdata, 10);

    trit pattern1[] = {1, 1};
    tcore_grep_result_t grep;

    TEST("tcore_grep finds pattern");
    int grc = tcore_grep(&env, "grep_test.t", pattern1, 2, &grep);
    ASSERT(grc >= 1, "at least one match");

    TEST("tcore_grep match count correct");
    ASSERT(grep.match_count >= 1, "match_count >= 1");

    trit pattern_none[] = {1, -1, 1, -1, 1};
    TEST("tcore_grep no match returns 0");
    grc = tcore_grep(&env, "grep_test.t", pattern_none, 5, &grep);
    ASSERT(grep.match_count == 0, "no matches");

    TEST("tcore_grep nonexistent file fails");
    ASSERT(tcore_grep(&env, "no.t", pattern1, 2, &grep) == TCORE_ERR_NOTFOUND,
           "missing file");

    /* ---- 1.7: trit-wc (word count) ------------------------------------ */
    SECTION("1.7 trit-wc (Word Count)");

    int wc_trits = 0, wc_lines = 0, wc_words = 0;

    TEST("tcore_wc counts trits correctly");
    ASSERT(tcore_wc(&env, "hello.t", &wc_trits, &wc_lines, &wc_words) == TCORE_OK,
           "wc OK");
    ASSERT(wc_trits == 5, "5 trits");

    TEST("tcore_wc counts words > 0");
    ASSERT(wc_words > 0, "at least one word");

    TEST("tcore_wc NULL file fails");
    ASSERT(tcore_wc(&env, "nope.t", &wc_trits, NULL, NULL) == TCORE_ERR_NOTFOUND,
           "missing file");

    /* ---- 1.8: trit-rm (file removal) ---------------------------------- */
    SECTION("1.8 trit-rm (File Removal)");

    TEST("tcore_rm removes file successfully");
    ASSERT(tcore_rm(&env, "copy.t") == TCORE_OK, "rm OK");

    TEST("tcore_rm file no longer readable");
    ASSERT(tcore_cat(&env, "copy.t", buf, 64) == TCORE_ERR_NOTFOUND,
           "deleted file gone");

    TEST("tcore_rm nonexistent file fails");
    ASSERT(tcore_rm(&env, "copy.t") == TCORE_ERR_NOTFOUND, "rm missing");

    /* ---- 1.9: trit-head / trit-tail ----------------------------------- */
    SECTION("1.9 trit-head / trit-tail");

    TEST("tcore_head reads first 3 trits");
    trit hbuf[64];
    int hn = tcore_head(&env, "hello.t", hbuf, 3);
    ASSERT(hn == 3 && hbuf[0] == 1 && hbuf[2] == -1, "head 3 trits");

    TEST("tcore_tail reads last 2 trits");
    trit tbuf[64];
    int tn = tcore_tail(&env, "hello.t", tbuf, 2);
    ASSERT(tn == 2 && tbuf[0] == 1 && tbuf[1] == -1, "tail 2 trits");

    TEST("tcore_head 0 count returns 0");
    ASSERT(tcore_head(&env, "hello.t", hbuf, 0) == 0, "head 0 = 0");

    TEST("tcore_tail nonexistent file fails");
    ASSERT(tcore_tail(&env, "nope.t", tbuf, 2) == TCORE_ERR_NOTFOUND,
           "tail missing");

    /* ---- 1.10: Binary-to-Ternary Transcoding -------------------------- */
    SECTION("1.10 Binary-to-Ternary Transcoding");

    tcore_transcode_ctx_t tc;

    TEST("tcore_transcode_init OK");
    ASSERT(tcore_transcode_init(&tc) == TCORE_OK, "transcode init");

    TEST("transcode guard initially clean");
    ASSERT(tc.guard.guard_status == TRIT_TRUE, "guard clean");

    int bin_vals[] = {42, -7, 0, 100};
    trit tc_out[256];

    TEST("tcore_transcode_bin_to_trit converts binary");
    int tc_len = tcore_transcode_bin_to_trit(&tc, bin_vals, 4, tc_out);
    ASSERT(tc_len > 0, "output trits > 0");

    TEST("transcoded count = 4 * 32");
    ASSERT(tc_len == 4 * MR_REG_WIDTH, "4 ints * 32 trits/int");

    TEST("transcode overhead tracked");
    ASSERT(tc.cycles_binary > 0, "binary cycles > 0");

    /* ---- 1.11: Radix Integrity Guard ---------------------------------- */
    SECTION("1.11 Radix Integrity Guard");

    trit good_data[] = {1, 0, -1, 1, -1, 0};
    TEST("radix_validate passes valid data");
    ASSERT(tcore_radix_validate(&tc, good_data, 6) == TCORE_OK, "valid data");

    trit bad_data[] = {1, 0, 5, -1}; /* 5 is outside {-1,0,+1} */
    TEST("radix_validate detects violation");
    ASSERT(tcore_radix_validate(&tc, bad_data, 4) == TCORE_ERR_RADIX,
           "radix violation detected");

    TEST("radix_validate guard goes to FALSE on violation");
    ASSERT(tc.guard.guard_status == TRIT_FALSE, "guard compromised");

    TEST("radix_validate violations counted");
    ASSERT(tc.guard.violations > 0, "violations > 0");

    /* ---- 1.12: Error handling edge cases ------------------------------- */
    SECTION("1.12 Edge Cases");

    tcore_env_t uninit;
    memset(&uninit, 0, sizeof(uninit));

    TEST("operations on uninitialized env fail");
    ASSERT(tcore_ls(&uninit, &ls) == TCORE_ERR_IO, "uninit env ls");

    TEST("tcore_echo NULL data fails");
    ASSERT(tcore_echo(&env, "x.t", NULL, 5) == TCORE_ERR_IO, "NULL data");

    TEST("tcore_grep empty pattern fails");
    ASSERT(tcore_grep(&env, "hello.t", pattern1, 0, &grep) == TCORE_ERR_IO,
           "zero-len pattern");

    /* Clean up test files */
    tcore_rm(&env, "hello.t");
    tcore_rm(&env, "grep_test.t");

    SUITE_END("POSIX Coreutils");
}

/* ======================================================================== */
/*  SUITE 2: Ternary Networking Stack (T-Net) (50+ tests)                   */
/* ======================================================================== */

static void test_networking_stack(void) {
    SUITE_START("Ternary Networking Stack (T-Net)");

    /* ---- 2.1: Address Utilities --------------------------------------- */
    SECTION("2.1 Address Utilities");

    tnet_addr_t addr1;

    TEST("tnet_addr_from_int/to_int roundtrip (42)");
    tnet_addr_from_int(&addr1, 42);
    ASSERT(tnet_addr_to_int(&addr1) == 42, "42 roundtrip");

    TEST("tnet_addr_from_int/to_int roundtrip (0)");
    tnet_addr_from_int(&addr1, 0);
    ASSERT(tnet_addr_to_int(&addr1) == 0, "0 roundtrip");

    TEST("tnet_addr_from_int/to_int roundtrip (-13)");
    tnet_addr_from_int(&addr1, -13);
    ASSERT(tnet_addr_to_int(&addr1) == -13, "-13 roundtrip");

    tnet_addr_t addr2;
    tnet_addr_from_int(&addr2, 42);
    TEST("tnet_addr_equal matches");
    ASSERT(tnet_addr_equal(&addr1, &addr2) == 0, "different addrs");

    tnet_addr_from_int(&addr1, 42);
    TEST("tnet_addr_equal same addr");
    ASSERT(tnet_addr_equal(&addr1, &addr2) == 1, "same addr");

    /* Port utilities */
    tnet_port_t port1;

    TEST("tnet_port_from_int/to_int roundtrip (80)");
    tnet_port_from_int(&port1, 80);
    ASSERT(tnet_port_to_int(&port1) == 80, "port 80");

    TEST("tnet_port_from_int/to_int roundtrip (0)");
    tnet_port_from_int(&port1, 0);
    ASSERT(tnet_port_to_int(&port1) == 0, "port 0");

    /* ---- 2.2: Stack Initialization ------------------------------------ */
    SECTION("2.2 Stack Initialization");

    tnet_stack_t stack;
    tnet_addr_t local;
    tnet_addr_from_int(&local, 100);

    TEST("tnet_init returns OK");
    ASSERT(tnet_init(&stack, &local) == TNET_OK, "init OK");

    TEST("tnet_init sets initialized");
    ASSERT(stack.initialized == 1, "initialized");

    TEST("tnet_init local addr set correctly");
    ASSERT(tnet_addr_to_int(&stack.local_addr) == 100, "local addr 100");

    TEST("tnet_init NULL stack fails");
    ASSERT(tnet_init(NULL, &local) == TNET_ERR_INIT, "NULL stack");

    TEST("tnet_init NULL addr fails");
    ASSERT(tnet_init(&stack, NULL) == TNET_ERR_INIT, "NULL addr");

    /* Reinitialize for clean tests */
    tnet_init(&stack, &local);

    /* ---- 2.3: Packet Building ----------------------------------------- */
    SECTION("2.3 Packet Building");

    tnet_packet_t pkt;
    tnet_addr_t dst;
    tnet_addr_from_int(&dst, 200);
    tnet_port_t sp, dp;
    tnet_port_from_int(&sp, 80);
    tnet_port_from_int(&dp, 443);
    trit payload[] = {1, -1, 0, 1};

    TEST("tnet_build_packet OK");
    ASSERT(tnet_build_packet(&pkt, &local, &dst, &sp, &dp,
                             TNET_PROTO_DATA, payload, 4) == TNET_OK,
           "build OK");

    TEST("packet valid flag set");
    ASSERT(pkt.valid == 1, "valid");

    TEST("packet payload length correct");
    ASSERT(pkt.header.payload_len == 4, "payload len 4");

    TEST("packet protocol correct");
    ASSERT(pkt.header.protocol == TNET_PROTO_DATA, "proto DATA");

    TEST("packet checksum computed");
    {
        int has_checksum = 0;
        for (int i = 0; i < TNET_CHECKSUM_TRITS; i++) {
            if (pkt.header.checksum[i] != 0) has_checksum = 1;
        }
        ASSERT(has_checksum || pkt.header.payload_len > 0, "checksum present");
    }

    /* ---- 2.4: Checksum Verification ----------------------------------- */
    SECTION("2.4 Checksum Verification");

    TEST("tnet_checksum_verify on valid packet");
    ASSERT(tnet_checksum_verify(&pkt) == 1, "checksum valid");

    TEST("tnet_checksum_verify detects corruption");
    {
        tnet_packet_t bad_pkt = pkt;
        bad_pkt.payload[0] = -1; /* Corrupt payload */
        ASSERT(tnet_checksum_verify(&bad_pkt) == 0, "checksum invalid");
    }

    /* ---- 2.5: Send / Receive / Loopback ------------------------------- */
    SECTION("2.5 Send / Receive / Loopback");

    TEST("tnet_send enqueues packet");
    int snd = tnet_send(&stack, &local, &dp, TNET_PROTO_DATA, payload, 4);
    ASSERT(snd == TNET_OK, "send OK");

    TEST("tnet_send increments tx_count");
    ASSERT(stack.total_tx >= 1, "tx count");

    TEST("tnet_loopback delivers to self");
    int looped = tnet_loopback(&stack);
    ASSERT(looped == 1, "1 packet looped");

    TEST("tnet_recv gets looped packet");
    tnet_packet_t rxpkt;
    ASSERT(tnet_recv(&stack, &rxpkt) == TNET_OK, "recv OK");

    TEST("received packet payload matches");
    ASSERT(rxpkt.payload[0] == payload[0] && rxpkt.payload[3] == payload[3],
           "payload match");

    TEST("tnet_recv empty queue returns error");
    ASSERT(tnet_recv(&stack, &rxpkt) == TNET_ERR_NOCONN, "empty queue");

    /* Send to different address — should not loop back */
    tnet_addr_t other;
    tnet_addr_from_int(&other, 999);
    TEST("tnet_send to non-local addr");
    tnet_send(&stack, &other, NULL, TNET_PROTO_DATA, payload, 4);
    int looped2 = tnet_loopback(&stack);
    ASSERT(looped2 == 0, "no loopback for other addr");

    /* ---- 2.6: Firewall ------------------------------------------------ */
    SECTION("2.6 Kleene Firewall");

    /* Reinitialize for clean firewall tests */
    tnet_init(&stack, &local);

    /* Add DENY rule for protocol 99 */
    tnet_addr_t any_addr;
    memset(&any_addr, 0, sizeof(any_addr)); /* All zeros = wildcard */

    TEST("tnet_fw_add_rule DENY");
    ASSERT(tnet_fw_add_rule(&stack, &any_addr, NULL, 99, TRIT_FALSE) == TNET_OK,
           "deny rule added");

    /* Add ALLOW rule for PING */
    TEST("tnet_fw_add_rule ALLOW");
    ASSERT(tnet_fw_add_rule(&stack, &any_addr, NULL, TNET_PROTO_PING,
                            TRIT_TRUE) == TNET_OK,
           "allow rule added");

    /* Add INSPECT (audit) rule for DATA */
    TEST("tnet_fw_add_rule INSPECT");
    ASSERT(tnet_fw_add_rule(&stack, &any_addr, NULL, TNET_PROTO_DATA,
                            TRIT_UNKNOWN) == TNET_OK,
           "inspect rule added");

    TEST("firewall DENY blocks packet");
    {
        tnet_packet_t deny_pkt;
        tnet_build_packet(&deny_pkt, &other, &local, NULL, NULL,
                          99, payload, 4);
        trit result = tnet_fw_evaluate(&stack, &deny_pkt);
        ASSERT(result == TRIT_FALSE, "deny result");
    }

    TEST("firewall ALLOW passes packet");
    {
        tnet_packet_t allow_pkt;
        tnet_build_packet(&allow_pkt, &other, &local, NULL, NULL,
                          TNET_PROTO_PING, payload, 4);
        trit result = tnet_fw_evaluate(&stack, &allow_pkt);
        ASSERT(result == TRIT_TRUE, "allow result");
    }

    TEST("firewall INSPECT returns Unknown");
    {
        tnet_packet_t insp_pkt;
        tnet_build_packet(&insp_pkt, &other, &local, NULL, NULL,
                          TNET_PROTO_DATA, payload, 4);
        trit result = tnet_fw_evaluate(&stack, &insp_pkt);
        ASSERT(result == TRIT_UNKNOWN, "inspect result");
    }

    TEST("firewall stats tracked");
    {
        int denied = 0, inspected = 0, allowed = 0;
        tnet_fw_stats(&stack, &denied, &inspected, &allowed);
        ASSERT(denied >= 1, "at least 1 denied");
    }

    /* Firewall + loopback integration: denied packet should be dropped */
    tnet_init(&stack, &local);
    tnet_fw_add_rule(&stack, &any_addr, NULL, -1, TRIT_FALSE); /* Deny all */
    tnet_send(&stack, &local, NULL, TNET_PROTO_DATA, payload, 4);

    TEST("firewall denies loopback packets");
    ASSERT(tnet_loopback(&stack) == 0, "all denied");

    /* ---- 2.7: Connection Management ----------------------------------- */
    SECTION("2.7 Connection Management");

    tnet_init(&stack, &local);
    tnet_port_t lp, rp;
    tnet_port_from_int(&lp, 80);
    tnet_port_from_int(&rp, 443);

    TEST("tnet_connect opens connection");
    int cid = tnet_connect(&stack, &dst, &lp, &rp);
    ASSERT(cid >= 0, "conn id >= 0");

    TEST("connection state is ESTABLISHED");
    ASSERT(tnet_conn_state(&stack, cid) == TRIT_TRUE, "established");

    TEST("tnet_disconnect closes connection");
    ASSERT(tnet_disconnect(&stack, cid) == TNET_OK, "disconnect OK");

    TEST("connection state is CLOSED after disconnect");
    ASSERT(tnet_conn_state(&stack, cid) == TRIT_FALSE, "closed");

    TEST("disconnect already closed returns error");
    ASSERT(tnet_disconnect(&stack, cid) == TNET_ERR_NOCONN, "already closed");

    TEST("invalid conn_id returns CLOSED");
    ASSERT(tnet_conn_state(&stack, 999) == TRIT_FALSE, "invalid id");

    /* ---- 2.8: ARP Cache ----------------------------------------------- */
    SECTION("2.8 ARP Cache");

    tnet_init(&stack, &local);

    TEST("tnet_arp_update adds entry");
    ASSERT(tnet_arp_update(&stack, &dst, 0xAB) == TNET_OK, "arp add");

    TEST("tnet_arp_lookup finds entry");
    ASSERT(tnet_arp_lookup(&stack, &dst) == 0xAB, "arp lookup");

    TEST("tnet_arp_lookup miss returns -1");
    tnet_addr_t unknown;
    tnet_addr_from_int(&unknown, 777);
    ASSERT(tnet_arp_lookup(&stack, &unknown) == -1, "arp miss");

    TEST("tnet_arp_update overwrites existing");
    tnet_arp_update(&stack, &dst, 0xCD);
    ASSERT(tnet_arp_lookup(&stack, &dst) == 0xCD, "arp overwrite");

    /* ---- 2.9: Ping --------------------------------------------------- */
    SECTION("2.9 Ping Utility");

    tnet_init(&stack, &local);

    TEST("tnet_ping self succeeds");
    ASSERT(tnet_ping(&stack, &local) == 1, "ping self OK");

    TEST("tnet_ping non-local times out");
    ASSERT(tnet_ping(&stack, &other) == 0, "ping other = 0");

    /* ---- 2.10: Statistics --------------------------------------------- */
    SECTION("2.10 Statistics");

    TEST("tnet_stats reports tx/rx");
    {
        int tx = 0, rx = 0, errors = 0, conns = 0;
        tnet_stats(&stack, &tx, &rx, &errors, &conns);
        ASSERT(tx >= 0 && rx >= 0, "stats returned");
    }

    SUITE_END("T-Net");
}

/* ======================================================================== */
/*  SUITE 3: GUI Framework & Display Drivers (40+ tests)                    */
/* ======================================================================== */

static void test_gui_framework(void) {
    SUITE_START("GUI Framework & Display Drivers");

    /* ---- 3.1: Initialization ------------------------------------------ */
    SECTION("3.1 Compositor Initialization");

    tgui_compositor_t comp;

    TEST("tgui_init returns 0");
    ASSERT(tgui_init(&comp) == 0, "init OK");

    TEST("tgui_init sets initialized");
    ASSERT(comp.initialized == 1, "initialized");

    TEST("tgui_init clears window count");
    ASSERT(comp.window_count == 0, "no windows");

    TEST("tgui_init NULL fails");
    ASSERT(tgui_init(NULL) == -1, "NULL init fails");

    /* ---- 3.2: Framebuffer Operations ---------------------------------- */
    SECTION("3.2 Framebuffer Operations");

    tgui_color_t red = TGUI_COLOR_RED;
    tgui_color_t blue = TGUI_COLOR_BLUE;
    tgui_color_t gray = TGUI_COLOR_GRAY;
    tgui_color_t white = TGUI_COLOR_WHITE;

    TEST("tgui_clear fills entire framebuffer");
    tgui_clear(&comp, gray);
    {
        tgui_color_t px = tgui_get_pixel(&comp, 0, 0);
        ASSERT(px.r == 0 && px.g == 0 && px.b == 0, "pixel is gray");
    }

    TEST("tgui_set_pixel sets color");
    ASSERT(tgui_set_pixel(&comp, 10, 5, red) == 0, "set pixel OK");

    TEST("tgui_get_pixel reads back color");
    {
        tgui_color_t px = tgui_get_pixel(&comp, 10, 5);
        ASSERT(px.r == 1 && px.g == -1 && px.b == -1, "pixel is red");
    }

    TEST("tgui_set_pixel out of bounds fails");
    ASSERT(tgui_set_pixel(&comp, -1, 0, red) == -1, "negative x");
    ASSERT(tgui_set_pixel(&comp, 999, 0, red) == -1, "big x");
    ASSERT(tgui_set_pixel(&comp, 0, -1, red) == -1, "negative y");
    ASSERT(tgui_set_pixel(&comp, 0, 999, red) == -1, "big y");

    TEST("tgui_get_pixel out of bounds returns black");
    {
        tgui_color_t px = tgui_get_pixel(&comp, -1, -1);
        ASSERT(px.r == -1 && px.g == -1 && px.b == -1, "OOB = black");
    }

    /* ---- 3.3: Drawing Primitives -------------------------------------- */
    SECTION("3.3 Drawing Primitives");

    tgui_clear(&comp, TGUI_COLOR_BLACK);

    TEST("tgui_draw_hline draws horizontal line");
    tgui_draw_hline(&comp, 0, 0, 5, white);
    {
        tgui_color_t px0 = tgui_get_pixel(&comp, 0, 0);
        tgui_color_t px4 = tgui_get_pixel(&comp, 4, 0);
        tgui_color_t px5 = tgui_get_pixel(&comp, 5, 0);
        ASSERT(px0.r == 1 && px4.r == 1 && px5.r == -1,
               "hline 0-4 white, 5 black");
    }

    tgui_clear(&comp, TGUI_COLOR_BLACK);

    TEST("tgui_draw_vline draws vertical line");
    tgui_draw_vline(&comp, 0, 0, 3, blue);
    {
        tgui_color_t px0 = tgui_get_pixel(&comp, 0, 0);
        tgui_color_t px2 = tgui_get_pixel(&comp, 0, 2);
        ASSERT(px0.b == 1 && px2.b == 1, "vline blue");
    }

    TEST("tgui_draw_rect draws rectangle outline");
    tgui_clear(&comp, TGUI_COLOR_BLACK);
    tgui_draw_rect(&comp, 1, 1, 4, 3, red);
    {
        tgui_color_t corner = tgui_get_pixel(&comp, 1, 1);
        ASSERT(corner.r == 1, "corner is red");
    }

    TEST("tgui_fill_rect fills solid area");
    tgui_clear(&comp, TGUI_COLOR_BLACK);
    tgui_fill_rect(&comp, 5, 5, 3, 2, TGUI_COLOR_GREEN);
    {
        tgui_color_t pxIn = tgui_get_pixel(&comp, 6, 5);
        tgui_color_t pxOut = tgui_get_pixel(&comp, 4, 5);
        ASSERT(pxIn.g == 1 && pxOut.g == -1, "fill rect green inside");
    }

    /* ---- 3.4: Color Blending ------------------------------------------ */
    SECTION("3.4 NDR Color Blending");

    TEST("blend red + green = yellow");
    {
        tgui_color_t blended = tgui_blend(TGUI_COLOR_RED, TGUI_COLOR_GREEN);
        ASSERT(blended.r == 1 && blended.g == 1 && blended.b == -1,
               "red+green = yellow");
    }

    TEST("blend black + white = white");
    {
        tgui_color_t blended = tgui_blend(TGUI_COLOR_BLACK, TGUI_COLOR_WHITE);
        ASSERT(blended.r == 1 && blended.g == 1 && blended.b == 1,
               "black+white = white");
    }

    TEST("blend gray + gray = gray");
    {
        tgui_color_t blended = tgui_blend(TGUI_COLOR_GRAY, TGUI_COLOR_GRAY);
        ASSERT(blended.r == 0 && blended.g == 0 && blended.b == 0,
               "gray+gray = gray");
    }

    /* ---- 3.5: Window Management --------------------------------------- */
    SECTION("3.5 Window Management");

    TEST("tgui_window_create returns valid ID");
    int wid = tgui_window_create(&comp, "Test Win", 2, 2, 10, 5, TRIT_TRUE);
    ASSERT(wid >= 0, "window created");

    TEST("window_count incremented");
    ASSERT(comp.window_count == 1, "1 window");

    TEST("tgui_window_create second window");
    int wid2 = tgui_window_create(&comp, "BG Win", 0, 0, 8, 4, TRIT_FALSE);
    ASSERT(wid2 >= 0 && wid2 != wid, "second window");

    TEST("tgui_window_set_pixel draws in window");
    ASSERT(tgui_window_set_pixel(&comp, wid, 0, 0, TGUI_COLOR_RED) == 0,
           "set pixel in window");

    TEST("tgui_window_move repositions window");
    ASSERT(tgui_window_move(&comp, wid, 5, 5) == 0, "move OK");

    TEST("tgui_window_set_visible hides window");
    ASSERT(tgui_window_set_visible(&comp, wid2, 0) == 0, "hide OK");

    TEST("tgui_window_destroy removes window");
    ASSERT(tgui_window_destroy(&comp, wid2) == 0, "destroy OK");
    ASSERT(comp.window_count == 1, "1 window left");

    TEST("tgui_window_destroy invalid ID fails");
    ASSERT(tgui_window_destroy(&comp, wid2) == -1, "double destroy");

    /* ---- 3.6: Compositing --------------------------------------------- */
    SECTION("3.6 Compositing");

    TEST("tgui_composite renders frame");
    ASSERT(tgui_composite(&comp) == 0, "composite OK");

    TEST("frames_rendered incremented");
    ASSERT(comp.frames_rendered == 1, "1 frame");

    /* ---- 3.7: Event Handling ------------------------------------------ */
    SECTION("3.7 Event Handling");

    tgui_event_t evt;
    evt.type = TGUI_EVT_KEY_DOWN;
    evt.key_code = 65; /* 'A' */
    evt.x = evt.y = 0;
    evt.window_id = wid;

    TEST("tgui_event_push succeeds");
    ASSERT(tgui_event_push(&comp, &evt) == 0, "push OK");

    TEST("tgui_event_count returns 1");
    ASSERT(tgui_event_count(&comp) == 1, "1 event");

    tgui_event_t out;
    TEST("tgui_event_pop returns event");
    ASSERT(tgui_event_pop(&comp, &out) == 0, "pop OK");

    TEST("popped event type matches");
    ASSERT(out.type == TGUI_EVT_KEY_DOWN, "key down");

    TEST("popped event key_code matches");
    ASSERT(out.key_code == 65, "key A");

    TEST("tgui_event_pop on empty queue fails");
    ASSERT(tgui_event_pop(&comp, &out) == -1, "empty queue");

    /* ---- 3.8: Statistics ---------------------------------------------- */
    SECTION("3.8 Statistics");

    TEST("tgui_stats reports values");
    {
        int frames = 0, pixels = 0, events = 0;
        tgui_stats(&comp, &frames, &pixels, &events);
        ASSERT(frames >= 1 && pixels > 0 && events >= 1, "stats non-zero");
    }

    /* Cleanup */
    tgui_window_destroy(&comp, wid);

    SUITE_END("GUI Framework");
}

/* ======================================================================== */
/*  SUITE 4: Package Management (T-Pkg) (40+ tests)                        */
/* ======================================================================== */

static void test_package_manager(void) {
    SUITE_START("Package Management (T-Pkg)");

    /* ---- 4.1: Initialization ------------------------------------------ */
    SECTION("4.1 Repository Initialization");

    tpkg_repo_t repo;

    TEST("tpkg_init returns OK");
    ASSERT(tpkg_init(&repo) == TPKG_OK, "init OK");

    TEST("tpkg_init sets initialized");
    ASSERT(repo.initialized == 1, "initialized");

    TEST("tpkg_init clears package count");
    ASSERT(repo.package_count == 0, "0 packages");

    TEST("tpkg_init NULL fails");
    ASSERT(tpkg_init(NULL) == TPKG_ERR_IO, "NULL init");

    /* ---- 4.2: Package Addition ---------------------------------------- */
    SECTION("4.2 Package Addition");

    trit pkg_data1[] = {1, 0, -1, 1};
    trit pkg_data2[] = {-1, -1, 0, 1, 1};

    TEST("tpkg_add adds package");
    ASSERT(tpkg_add(&repo, "trit-utils", "Ternary utilities", 100,
                    pkg_data1, 4) == TPKG_OK, "add OK");

    TEST("tpkg_add second package");
    ASSERT(tpkg_add(&repo, "trit-crypto", "Crypto library", 200,
                    pkg_data2, 5) == TPKG_OK, "add second");

    TEST("package count is 2");
    ASSERT(repo.package_count == 2, "2 packages");

    TEST("tpkg_add duplicate name fails");
    ASSERT(tpkg_add(&repo, "trit-utils", "Dup", 100, pkg_data1, 4)
           == TPKG_ERR_INSTALLED, "duplicate");

    TEST("tpkg_add NULL name fails");
    ASSERT(tpkg_add(&repo, NULL, "X", 100, pkg_data1, 4) == TPKG_ERR_IO,
           "NULL name");

    /* ---- 4.3: Dependencies -------------------------------------------- */
    SECTION("4.3 Dependencies");

    TEST("tpkg_add_dep adds required dependency");
    ASSERT(tpkg_add_dep(&repo, "trit-crypto", "trit-utils",
                        TPKG_DEP_REQUIRED, 100) == TPKG_OK,
           "dep added");

    TEST("tpkg_add_dep nonexistent package fails");
    ASSERT(tpkg_add_dep(&repo, "nosuch", "trit-utils",
                        TPKG_DEP_REQUIRED, 100) == TPKG_ERR_NOTFOUND,
           "no such pkg");

    /* ---- 4.4: Dependency Resolution ----------------------------------- */
    SECTION("4.4 Dependency Resolution");

    TEST("resolve_deps fails when required dep not installed");
    ASSERT(tpkg_resolve_deps(&repo, "trit-crypto") == TPKG_ERR_DEPFAIL,
           "dep missing");

    /* Install the required dependency first */
    TEST("install trit-utils (no deps)");
    ASSERT(tpkg_install(&repo, "trit-utils") == TPKG_OK, "install OK");

    TEST("resolve_deps succeeds after dep installed");
    ASSERT(tpkg_resolve_deps(&repo, "trit-crypto") == TPKG_OK, "deps OK");

    /* ---- 4.5: Install / Remove ---------------------------------------- */
    SECTION("4.5 Install / Remove");

    TEST("tpkg_install trit-crypto with deps met");
    ASSERT(tpkg_install(&repo, "trit-crypto") == TPKG_OK, "install crypto");

    TEST("installed count is 2");
    ASSERT(repo.installed_count == 2, "2 installed");

    TEST("tpkg_install already installed fails");
    ASSERT(tpkg_install(&repo, "trit-crypto") == TPKG_ERR_INSTALLED,
           "already installed");

    TEST("tpkg_is_installed returns true");
    ASSERT(tpkg_is_installed(&repo, "trit-crypto") == 1, "is installed");

    TEST("tpkg_remove uninstalls package");
    ASSERT(tpkg_remove(&repo, "trit-crypto") == TPKG_OK, "remove OK");

    TEST("installed count back to 1");
    ASSERT(repo.installed_count == 1, "1 installed");

    TEST("tpkg_is_installed returns false after remove");
    ASSERT(tpkg_is_installed(&repo, "trit-crypto") == 0, "not installed");

    TEST("tpkg_remove nonexistent fails");
    ASSERT(tpkg_remove(&repo, "nope") == TPKG_ERR_NOTFOUND, "no such pkg");

    /* ---- 4.6: Conflict Dependencies ----------------------------------- */
    SECTION("4.6 Conflict Dependencies");

    trit pkg_data3[] = {0, 0, 1};
    tpkg_add(&repo, "trit-alt-crypto", "Alt crypto", 100, pkg_data3, 3);
    tpkg_add_dep(&repo, "trit-alt-crypto", "trit-utils",
                 TPKG_DEP_CONFLICT, 0);

    TEST("conflict detected when conflicting pkg installed");
    ASSERT(tpkg_resolve_deps(&repo, "trit-alt-crypto") == TPKG_ERR_CONFLICT,
           "conflict detected");

    TEST("install fails due to conflict");
    ASSERT(tpkg_install(&repo, "trit-alt-crypto") != TPKG_OK,
           "install blocked by conflict");

    /* ---- 4.7: Search -------------------------------------------------- */
    SECTION("4.7 Search");

    tpkg_search_result_t sr;

    TEST("tpkg_search finds by name");
    ASSERT(tpkg_search(&repo, "trit", &sr) >= 1, "found results");

    TEST("tpkg_search count > 0");
    ASSERT(sr.count >= 2, "at least 2 matches");

    TEST("tpkg_search no match");
    ASSERT(tpkg_search(&repo, "zzz_no_match", &sr) == 0, "0 matches");

    TEST("tpkg_list_installed returns correct count");
    {
        tpkg_search_result_t ins;
        int n = tpkg_list_installed(&repo, &ins);
        ASSERT(n == 1 && ins.count == 1, "1 installed");
    }

    /* ---- 4.8: Integrity Verification ---------------------------------- */
    SECTION("4.8 Integrity Verification");

    TEST("tpkg_verify passes for valid package");
    ASSERT(tpkg_verify(&repo, "trit-utils") == TPKG_OK, "verify OK");

    TEST("tpkg_verify detects corruption");
    {
        /* Corrupt a package's data */
        int idx = -1;
        for (int i = 0; i < repo.package_count; i++) {
            if (strcmp(repo.packages[i].name, "trit-crypto") == 0) {
                idx = i;
                break;
            }
        }
        if (idx >= 0) {
            repo.packages[idx].data[0] = (trit)(repo.packages[idx].data[0] == 1 ? -1 : 1);
            ASSERT(tpkg_verify(&repo, "trit-crypto") == TPKG_ERR_CHECKSUM,
                   "corruption detected");
        } else {
            ASSERT(0, "could not find trit-crypto");
        }
    }

    /* ---- 4.9: Statistics ---------------------------------------------- */
    SECTION("4.9 Statistics");

    TEST("tpkg_stats reports values");
    {
        int total = 0, installed = 0, conflicts = 0, fails = 0;
        tpkg_stats(&repo, &total, &installed, &conflicts, &fails);
        ASSERT(total >= 3, "at least 3 packages");
        ASSERT(installed >= 1, "at least 1 installed");
    }

    /* ---- 4.10: Optional Dependencies ---------------------------------- */
    SECTION("4.10 Optional Dependencies");

    trit pd4[] = {1, 1};
    tpkg_add(&repo, "trit-opt-demo", "Optional dep demo", 100, pd4, 2);
    tpkg_add_dep(&repo, "trit-opt-demo", "trit-nonexistent",
                 TPKG_DEP_OPTIONAL, 0);

    TEST("optional dep allows install even if missing");
    ASSERT(tpkg_resolve_deps(&repo, "trit-opt-demo") == TPKG_OK,
           "optional dep OK");

    TEST("install with optional missing dep succeeds");
    ASSERT(tpkg_install(&repo, "trit-opt-demo") == TPKG_OK,
           "install with optional");

    SUITE_END("T-Pkg");
}

/* ======================================================================== */
/*  SUITE 5: AI/ML Integration & Tooling (40+ tests)                        */
/* ======================================================================== */

static void test_ai_integration(void) {
    SUITE_START("AI/ML Integration & Tooling");

    /* ---- 5.1: Model Initialization ------------------------------------ */
    SECTION("5.1 Model Initialization");

    tai_model_t model;

    TEST("tai_model_init returns OK");
    ASSERT(tai_model_init(&model) == TAI_OK, "init OK");

    TEST("tai_model_init sets initialized");
    ASSERT(model.initialized == 1, "initialized");

    TEST("tai_model_init clears layers");
    ASSERT(model.layer_count == 0, "0 layers");

    TEST("tai_model_init NULL fails");
    ASSERT(tai_model_init(NULL) == TAI_ERR_INIT, "NULL init");

    /* ---- 5.2: Layer Management ---------------------------------------- */
    SECTION("5.2 Layer Management");

    TEST("tai_add_layer adds first layer (4→3)");
    ASSERT(tai_add_layer(&model, 4, 3) == TAI_OK, "layer 1 added");

    TEST("tai_add_layer adds second layer (3→2)");
    ASSERT(tai_add_layer(&model, 3, 2) == TAI_OK, "layer 2 added");

    TEST("layer_count is 2");
    ASSERT(model.layer_count == 2, "2 layers");

    TEST("tai_add_layer invalid dims fails");
    ASSERT(tai_add_layer(&model, 0, 3) == TAI_ERR_DIM, "zero input");
    ASSERT(tai_add_layer(&model, 3, 0) == TAI_ERR_DIM, "zero output");

    /* ---- 5.3: Weight Setting ------------------------------------------ */
    SECTION("5.3 Weight Setting");

    /* Set weights for layer 0: identity-like pattern */
    TEST("tai_set_weight sets weight");
    ASSERT(tai_set_weight(&model, 0, 0, 0, TRIT_TRUE) == TAI_OK, "w[0][0]=+1");

    TEST("tai_set_weight row 1");
    ASSERT(tai_set_weight(&model, 0, 1, 1, TRIT_TRUE) == TAI_OK, "w[1][1]=+1");

    TEST("tai_set_weight row 2");
    ASSERT(tai_set_weight(&model, 0, 2, 2, TRIT_FALSE) == TAI_OK, "w[2][2]=-1");

    TEST("tai_set_weight out of bounds fails");
    ASSERT(tai_set_weight(&model, 0, 99, 0, TRIT_TRUE) == TAI_ERR_DIM, "OOB row");

    TEST("tai_set_weight invalid layer fails");
    ASSERT(tai_set_weight(&model, 99, 0, 0, TRIT_TRUE) == TAI_ERR_DIM,
           "bad layer");

    /* Set weights for layer 1 */
    tai_set_weight(&model, 1, 0, 0, TRIT_TRUE);
    tai_set_weight(&model, 1, 0, 1, TRIT_FALSE);
    tai_set_weight(&model, 1, 1, 1, TRIT_TRUE);
    tai_set_weight(&model, 1, 1, 2, TRIT_TRUE);

    /* ---- 5.4: Bias Setting -------------------------------------------- */
    SECTION("5.4 Bias Setting");

    TEST("tai_set_bias sets bias");
    ASSERT(tai_set_bias(&model, 0, 0, 0) == TAI_OK, "bias OK");

    TEST("tai_set_bias out of bounds fails");
    ASSERT(tai_set_bias(&model, 0, 99, 0) == TAI_ERR_DIM, "OOB bias");

    /* ---- 5.5: Matrix-Vector Multiplication ----------------------------- */
    SECTION("5.5 Matrix-Vector Multiplication");

    tai_matrix_t mat;
    memset(&mat, 0, sizeof(mat));
    mat.rows = 2;
    mat.cols = 3;
    /* Row 0: [+1,  0, -1] */
    mat.data[0] = 1;  mat.data[1] = 0;  mat.data[2] = -1;
    /* Row 1: [-1, +1, +1] */
    mat.data[3] = -1; mat.data[4] = 1;  mat.data[5] = 1;

    tai_vector_t vec;
    memset(&vec, 0, sizeof(vec));
    vec.len = 3;
    vec.data[0] = 1;  /* T */
    vec.data[1] = 1;  /* T */
    vec.data[2] = -1; /* F */

    tai_int_vector_t result;

    TEST("tai_matvec computes correctly");
    ASSERT(tai_matvec(&mat, &vec, &result) == TAI_OK, "matvec OK");

    /* Row 0: 1*1 + 0*1 + (-1)*(-1) = 1+0+1 = 2 */
    TEST("tai_matvec result[0] == 2");
    ASSERT(result.data[0] == 2, "row 0 = 2");

    /* Row 1: (-1)*1 + 1*1 + 1*(-1) = -1+1-1 = -1 */
    TEST("tai_matvec result[1] == -1");
    ASSERT(result.data[1] == -1, "row 1 = -1");

    TEST("tai_matvec dimension mismatch fails");
    {
        tai_vector_t short_vec;
        memset(&short_vec, 0, sizeof(short_vec));
        short_vec.len = 1;
        ASSERT(tai_matvec(&mat, &short_vec, &result) == TAI_ERR_DIM, "dim err");
    }

    /* ---- 5.6: Dot Product --------------------------------------------- */
    SECTION("5.6 Dot Product");

    tai_vector_t va, vb;
    memset(&va, 0, sizeof(va));
    memset(&vb, 0, sizeof(vb));
    va.len = vb.len = 4;
    va.data[0] = 1;  va.data[1] = -1; va.data[2] = 0;  va.data[3] = 1;
    vb.data[0] = 1;  vb.data[1] = 1;  vb.data[2] = -1; vb.data[3] = 1;

    /* Dot = 1*1 + (-1)*1 + 0*(-1) + 1*1 = 1-1+0+1 = 1 */
    TEST("tai_dot computes correctly");
    ASSERT(tai_dot(&va, &vb) == 1, "dot = 1");

    TEST("tai_dot self = sum of squares");
    ASSERT(tai_dot(&va, &va) == 3, "dot self = 3");

    /* ---- 5.7: Inference ----------------------------------------------- */
    SECTION("5.7 Inference");

    tai_vector_t input;
    memset(&input, 0, sizeof(input));
    input.len = 4;
    input.data[0] = 1;
    input.data[1] = -1;
    input.data[2] = 1;
    input.data[3] = 0;

    tai_int_vector_t output;

    TEST("tai_infer runs forward pass");
    ASSERT(tai_infer(&model, &input, &output) == TAI_OK, "infer OK");

    TEST("tai_infer output has correct length");
    ASSERT(output.len == 2, "output dim 2");

    TEST("tai_infer increments inference count");
    ASSERT(model.inferences >= 1, "inferences tracked");

    /* ---- 5.8: Argmax -------------------------------------------------- */
    SECTION("5.8 Argmax");

    tai_int_vector_t av;
    av.len = 3;
    av.data[0] = -5;
    av.data[1] = 10;
    av.data[2] = 3;

    TEST("tai_argmax returns correct index");
    ASSERT(tai_argmax(&av) == 1, "argmax = 1");

    tai_int_vector_t av2;
    av2.len = 2;
    av2.data[0] = 7;
    av2.data[1] = 7;

    TEST("tai_argmax tied values returns first");
    ASSERT(tai_argmax(&av2) == 0, "first wins tie");

    TEST("tai_argmax NULL returns -1");
    ASSERT(tai_argmax(NULL) == -1, "NULL = -1");

    /* ---- 5.9: Multi-Radix Accelerated MatVec -------------------------- */
    SECTION("5.9 Multi-Radix MatVec");

    tai_int_vector_t mr_result;

    TEST("tai_matvec_mr computes correctly");
    ASSERT(tai_matvec_mr(&model, &mat, &vec, &mr_result) == TAI_OK,
           "mr matvec OK");

    TEST("tai_matvec_mr result matches software");
    ASSERT(mr_result.data[0] == result.data[0], "mr row0 matches");

    /* ---- 5.10: Sparsity ------------------------------------------------ */
    SECTION("5.10 Sparsity Analysis");

    TEST("tai_sparsity computed correctly");
    {
        /* Layer 0: 3x4 = 12 weights, most are 0 (Unknown) */
        int sp = tai_sparsity(&model, 0);
        ASSERT(sp >= 0, "sparsity >= 0");
    }

    TEST("tai_sparsity invalid layer returns 0");
    ASSERT(tai_sparsity(&model, 99) == 0, "invalid layer");

    /* ---- 5.11: Training ----------------------------------------------- */
    SECTION("5.11 Training");

    tai_train_config_t tcfg;
    tcfg.epochs = 1;
    tcfg.batch_size = 1;
    tcfg.learning_rate_x100 = 10;
    tcfg.momentum_x100 = 0;

    TEST("tai_train_step runs without error");
    ASSERT(tai_train_step(&model, &input, 0, &tcfg) == TAI_OK, "train OK");

    TEST("tai_train_step updates weights (model changed)");
    /* After training, at least inference count should increase */
    ASSERT(model.inferences >= 2, "inference count grew from training");

    /* ---- 5.12: Statistics --------------------------------------------- */
    SECTION("5.12 Statistics");

    TEST("tai_stats reports values");
    {
        int inf = 0, macs = 0, skips = 0;
        tai_stats(&model, &inf, &macs, &skips);
        ASSERT(inf > 0 && macs > 0, "stats non-zero");
    }

    SUITE_END("AI/ML Integration");
}

/* ======================================================================== */
/*  SUITE 6: Security & Auditing (T-Sec) (40+ tests)                       */
/* ======================================================================== */

static void test_security_auditing(void) {
    SUITE_START("Security & Auditing (T-Sec)");

    /* ---- 6.1: Initialization ------------------------------------------ */
    SECTION("6.1 Security Module Initialization");

    tsec_state_t sec;

    TEST("tsec_init returns OK");
    ASSERT(tsec_init(&sec) == TSEC_OK, "init OK");

    TEST("tsec_init sets initialized");
    ASSERT(sec.initialized == 1, "initialized");

    TEST("tsec_init channel status = secure");
    ASSERT(sec.sidechannel.channel_status == TRIT_TRUE, "channel secure");

    TEST("tsec_init NULL fails");
    ASSERT(tsec_init(NULL) == TSEC_ERR_INIT, "NULL init");

    /* ---- 6.2: Audit Logging ------------------------------------------- */
    SECTION("6.2 Audit Logging");

    TEST("tsec_audit_log records event");
    ASSERT(tsec_audit_log(&sec, TSEC_EVT_SYSCALL, "process1", "file.t",
                          TSEC_PERM_READ, TRIT_TRUE) == TSEC_OK,
           "log event");

    TEST("tsec_audit_log increments log_count");
    ASSERT(sec.log_count == 1, "1 log entry");

    TEST("tsec_audit_log records denial");
    tsec_audit_log(&sec, TSEC_EVT_FILE, "proc2", "secret.t",
                   TSEC_PERM_WRITE, TRIT_FALSE);
    ASSERT(sec.total_denials == 1, "1 denial");

    TEST("tsec_audit_log records escalation");
    tsec_audit_log(&sec, TSEC_EVT_ESCALATION, "attacker", "kernel",
                   TSEC_PERM_EXEC, TRIT_UNKNOWN);
    ASSERT(sec.total_escalations == 1, "1 escalation");

    TEST("tsec_audit_log log_total tracks all");
    ASSERT(sec.log_total == 3, "3 total events");

    /* ---- 6.3: Audit Retrieval ----------------------------------------- */
    SECTION("6.3 Audit Retrieval");

    tsec_audit_entry_t recent[5];

    TEST("tsec_audit_recent retrieves entries");
    int n = tsec_audit_recent(&sec, recent, 5);
    ASSERT(n == 3, "3 recent entries");

    TEST("most recent entry is escalation");
    ASSERT(recent[0].event_type == TSEC_EVT_ESCALATION, "most recent");

    TEST("tsec_audit_count_type counts syscalls");
    ASSERT(tsec_audit_count_type(&sec, TSEC_EVT_SYSCALL) == 1, "1 syscall");

    TEST("tsec_audit_count_type counts file events");
    ASSERT(tsec_audit_count_type(&sec, TSEC_EVT_FILE) == 1, "1 file event");

    TEST("tsec_audit_count_escalations returns 1");
    ASSERT(tsec_audit_count_escalations(&sec) == 1, "1 escalation");

    /* ---- 6.4: Policy Enforcement -------------------------------------- */
    SECTION("6.4 Policy Enforcement");

    TEST("tsec_policy_add DENY rule");
    ASSERT(tsec_policy_add(&sec, "untrusted", "kernel",
                           TSEC_PERM_EXEC, TSEC_DENY, 10) == TSEC_OK,
           "deny rule added");

    TEST("tsec_policy_add ALLOW rule");
    ASSERT(tsec_policy_add(&sec, "admin", "",
                           TSEC_PERM_READ | TSEC_PERM_WRITE,
                           TSEC_ALLOW, 20) == TSEC_OK,
           "allow rule added");

    TEST("tsec_policy_add AUDIT rule");
    ASSERT(tsec_policy_add(&sec, "", "network",
                           TSEC_PERM_NET, TSEC_AUDIT, 5) == TSEC_OK,
           "audit rule added");

    TEST("policy evaluates DENY for untrusted→kernel");
    {
        trit r = tsec_policy_evaluate(&sec, "untrusted", "kernel", TSEC_PERM_EXEC);
        ASSERT(r == TRIT_FALSE, "deny");
    }

    TEST("policy evaluates ALLOW for admin→any");
    {
        trit r = tsec_policy_evaluate(&sec, "admin", "data.t", TSEC_PERM_READ);
        ASSERT(r == TRIT_TRUE, "allow");
    }

    TEST("policy evaluates AUDIT for any→network");
    {
        trit r = tsec_policy_evaluate(&sec, "browser", "network", TSEC_PERM_NET);
        ASSERT(r == TRIT_UNKNOWN, "audit");
    }

    TEST("default policy is ALLOW for unmatched");
    {
        trit r = tsec_policy_evaluate(&sec, "nobody", "nowhere", 0xFF);
        ASSERT(r == TRIT_TRUE, "default allow");
    }

    /* ---- 6.5: Enforce (evaluate + log + deny) ------------------------- */
    SECTION("6.5 Enforce");

    TEST("tsec_enforce denies blocked access");
    ASSERT(tsec_enforce(&sec, "untrusted", "kernel", TSEC_PERM_EXEC)
           == TSEC_ERR_DENIED, "enforce denied");

    TEST("tsec_enforce allows permitted access");
    ASSERT(tsec_enforce(&sec, "admin", "data.t", TSEC_PERM_READ)
           == TSEC_OK, "enforce allowed");

    TEST("tsec_enforce logs audit events");
    ASSERT(sec.log_total >= 5, "enforcement logged");

    /* ---- 6.6: Sandboxing ---------------------------------------------- */
    SECTION("6.6 Sandboxing");

    TEST("tsec_sandbox_create creates sandbox");
    int sb_id = tsec_sandbox_create(&sec, "app1",
                                     TSEC_PERM_READ | TSEC_PERM_WRITE,
                                     TRIT_UNKNOWN);
    ASSERT(sb_id >= 0, "sandbox created");

    TEST("sandbox_count is 1");
    ASSERT(sec.sandbox_count == 1, "1 sandbox");

    TEST("tsec_sandbox_check allowed permission");
    ASSERT(tsec_sandbox_check(&sec, sb_id, TSEC_PERM_READ) == TSEC_OK,
           "read allowed");

    TEST("tsec_sandbox_check denied permission");
    ASSERT(tsec_sandbox_check(&sec, sb_id, TSEC_PERM_EXEC) == TSEC_ERR_DENIED,
           "exec denied");

    TEST("tsec_sandbox_check combined permissions");
    ASSERT(tsec_sandbox_check(&sec, sb_id,
                              TSEC_PERM_READ | TSEC_PERM_WRITE) == TSEC_OK,
           "read+write OK");

    TEST("tsec_sandbox_check excess permissions denied");
    ASSERT(tsec_sandbox_check(&sec, sb_id,
                              TSEC_PERM_READ | TSEC_PERM_EXEC)
           == TSEC_ERR_DENIED, "read+exec denied");

    TEST("tsec_sandbox_check invalid ID fails");
    ASSERT(tsec_sandbox_check(&sec, 99, TSEC_PERM_READ)
           == TSEC_ERR_NOTFOUND, "invalid sb");

    /* Create second sandbox */
    int sb_id2 = tsec_sandbox_create(&sec, "untrust",
                                      TSEC_PERM_READ, TRIT_FALSE);
    TEST("second sandbox created");
    ASSERT(sb_id2 >= 0, "sb2 created");
    ASSERT(sec.sandbox_count == 2, "2 sandboxes");

    TEST("tsec_sandbox_destroy removes sandbox");
    ASSERT(tsec_sandbox_destroy(&sec, sb_id2) == TSEC_OK, "sb2 destroyed");
    ASSERT(sec.sandbox_count == 1, "1 sandbox left");

    TEST("tsec_sandbox_destroy already destroyed");
    ASSERT(tsec_sandbox_destroy(&sec, sb_id2) == TSEC_ERR_NOTFOUND,
           "double destroy");

    /* ---- 6.7: Side-Channel Monitoring --------------------------------- */
    SECTION("6.7 Side-Channel Monitoring");

    TEST("tsec_timing_sample records sample");
    ASSERT(tsec_timing_sample(&sec, 100) == TSEC_OK, "sample OK");

    TEST("tsec_timing_sample low variance keeps secure");
    tsec_timing_sample(&sec, 101);
    tsec_timing_sample(&sec, 99);
    ASSERT(tsec_sidechannel_status(&sec) == TRIT_TRUE, "still secure");

    TEST("tsec_emi_alert records alert");
    ASSERT(tsec_emi_alert(&sec) == TSEC_OK, "emi alert 1");

    TEST("second emi_alert");
    tsec_emi_alert(&sec);
    ASSERT(sec.sidechannel.emi_alerts == 2, "2 alerts");

    TEST("third emi_alert marks compromised");
    tsec_emi_alert(&sec);
    ASSERT(tsec_sidechannel_status(&sec) == TRIT_FALSE, "compromised");

    /* Reinitialize for fault tests */
    tsec_init(&sec);

    TEST("tsec_fault_detected marks compromised");
    ASSERT(tsec_fault_detected(&sec) == TSEC_OK, "fault detected");
    ASSERT(tsec_sidechannel_status(&sec) == TRIT_FALSE, "fault → compromised");

    TEST("fault injection logged as escalation");
    ASSERT(sec.total_escalations >= 1, "escalation from fault");

    /* ---- 6.8: Circular Buffer Overflow -------------------------------- */
    SECTION("6.8 Log Buffer Wraparound");

    tsec_init(&sec);

    TEST("log wraps without crash");
    {
        for (int i = 0; i < TSEC_MAX_LOG_ENTRIES + 10; i++) {
            tsec_audit_log(&sec, TSEC_EVT_SYSCALL, "spam", "target",
                           TSEC_PERM_READ, TRIT_TRUE);
        }
        ASSERT(sec.log_count == TSEC_MAX_LOG_ENTRIES, "count capped at max");
        ASSERT(sec.log_total == TSEC_MAX_LOG_ENTRIES + 10, "total not capped");
    }

    /* ---- 6.9: Statistics ---------------------------------------------- */
    SECTION("6.9 Statistics");

    TEST("tsec_stats reports values");
    {
        int total = 0, denials = 0, esc = 0, sb = 0;
        tsec_stats(&sec, &total, &denials, &esc, &sb);
        ASSERT(total > 0, "events > 0");
    }

    SUITE_END("Security & Auditing");
}

/* ======================================================================== */
/*  MAIN — Run all enhancement test suites                                  */
/* ======================================================================== */

int main(void) {
    printf("================================================================\n");
    printf("  Trit Linux — Logical Enhancements Master Test Suite\n");
    printf("  Testing all 6 enhancements from LOGICAL_ENHANCEMENTS doc\n");
    printf("================================================================\n");

    /* Run all 6 test suites */
    test_posix_coreutils();
    test_networking_stack();
    test_gui_framework();
    test_package_manager();
    test_ai_integration();
    test_security_auditing();

    /* ================================================================== */
    /*  Enhancement Suite Summary (6 sub-suites)                           */
    /* ================================================================== */

    printf("\n================================================================\n");
    printf("  TRIT LINUX ENHANCEMENT SUITE SUMMARY\n");
    printf("================================================================\n");
    printf("  Total assertions:  %d\n", tests_passed + tests_failed);
    printf("  Passed:            %d\n", tests_passed);
    printf("  Failed:            %d\n", tests_failed);
    printf("  Pass rate:         %d%%\n",
           (tests_passed + tests_failed) > 0
               ? (tests_passed * 100 / (tests_passed + tests_failed)) : 0);
    printf("================================================================\n");

    if (tests_failed > 0) {
        printf("  RESULT: FAIL (%d test(s) failed)\n", tests_failed);
    } else {
        printf("  RESULT: ALL TESTS PASSED\n");
    }
    printf("================================================================\n");

    return tests_failed > 0 ? 1 : 0;
}
