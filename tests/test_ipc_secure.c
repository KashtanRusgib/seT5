/**
 * @file test_ipc_secure.c
 * @brief seT6 — Secure Inter-Module Communication Test Suite
 *
 * Tests the Arch Linux–inspired secure IPC framework:
 *   - Ternary socket creation and activation
 *   - Socket send/recv with capability checks
 *   - Namespace isolation (user, net, ipc)
 *   - Capability grant and verification
 *   - Injection attack simulation and detection
 *   - Unknown state pause behavior
 *
 * Target: 40+ assertions.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "set5/trit.h"
#include "set5/tipc.h"
#include "set5/trit_ipc_secure.h"

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
    SECTION("Secure IPC Initialization");

    tipc_secure_t sec;

    TEST("Init returns OK");
    ASSERT(tipc_sec_init(&sec) == TIPC_SEC_OK, "init failed");

    TEST("Socket count starts at 0");
    ASSERT(sec.socket_count == 0, "expected 0");

    TEST("Namespace count starts at 0");
    ASSERT(sec.ns_count == 0, "expected 0");

    TEST("Capability count starts at 0");
    ASSERT(sec.cap_count == 0, "expected 0");

    TEST("Init with NULL");
    ASSERT(tipc_sec_init(NULL) == TIPC_SEC_ERR_INIT, "expected ERR_INIT");
}

/* ======================================================================== */
/*  Test: Ternary Socket Activation                                         */
/* ======================================================================== */

static void test_sockets(void) {
    SECTION("Ternary Socket Activation");

    tipc_secure_t sec;
    tipc_sec_init(&sec);

    TEST("Create socket 'tipc_main'");
    int sid = tipc_socket_create(&sec, "tipc_main", 0);
    ASSERT(sid == 0, "expected socket id 0");

    TEST("Socket starts in LISTENING state");
    ASSERT(sec.sockets[0].state == TSOCK_STATE_LISTENING, "expected LISTENING");

    TEST("Activation status is UNKNOWN (pending)");
    ASSERT(sec.sockets[0].activation_status == TRIT_UNKNOWN, "expected UNKNOWN");

    TEST("Activate socket");
    ASSERT(tipc_socket_activate(&sec, 0) == TIPC_SEC_OK, "activate failed");

    TEST("Socket now ACTIVATED");
    ASSERT(sec.sockets[0].state == TSOCK_STATE_ACTIVATED, "expected ACTIVATED");

    TEST("Activation status is TRUE");
    ASSERT(sec.sockets[0].activation_status == TRIT_TRUE, "expected TRUE");

    TEST("Create second socket");
    sid = tipc_socket_create(&sec, "tipc_aux", 1);
    ASSERT(sid == 1 && sec.socket_count == 2, "expected 2 sockets");

    TEST("Activate non-existent socket");
    ASSERT(tipc_socket_activate(&sec, 99) == TIPC_SEC_ERR_NOTFOUND,
           "expected ERR_NOTFOUND");
}

/* ======================================================================== */
/*  Test: Send / Recv with Capabilities                                     */
/* ======================================================================== */

static void test_send_recv(void) {
    SECTION("Socket Send / Recv with Capabilities");

    tipc_secure_t sec;
    tipc_sec_init(&sec);
    tipc_socket_create(&sec, "data_channel", 0);
    tipc_socket_activate(&sec, 0);

    trit data[] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE, TRIT_FALSE};

    TEST("Send without IPC_SEND cap — denied");
    ASSERT(tipc_socket_send(&sec, 0, data, 5, 0) == TIPC_SEC_ERR_DENIED,
           "expected DENIED");

    TEST("Send with IPC_SEND cap — succeeds");
    int sent = tipc_socket_send(&sec, 0, data, 5, TCAP_IPC_SEND);
    ASSERT(sent == 5, "expected 5 trits sent");

    TEST("Unknown pause detected (data has Unknown trit)");
    ASSERT(sec.unknown_pauses == 1, "expected 1 unknown pause");

    TEST("Recv data from socket");
    trit out[16] = {0};
    int recvd = tipc_socket_recv(&sec, 0, out, 16);
    ASSERT(recvd == 5, "expected 5 trits received");

    TEST("Received data matches sent data");
    ASSERT(out[0] == TRIT_TRUE && out[1] == TRIT_FALSE && out[2] == TRIT_UNKNOWN,
           "data mismatch");

    TEST("Buffer cleared after recv");
    ASSERT(tipc_socket_recv(&sec, 0, out, 16) == 0, "expected empty buffer");

    TEST("Total messages count");
    ASSERT(sec.total_messages == 1, "expected 1 message");
}

/* ======================================================================== */
/*  Test: Namespace Isolation                                               */
/* ======================================================================== */

static void test_namespaces(void) {
    SECTION("Namespace Isolation");

    tipc_secure_t sec;
    tipc_sec_init(&sec);

    TEST("Create user namespace");
    int ns_user = tipc_namespace_create(&sec, "ns_user", TNS_TYPE_USER);
    ASSERT(ns_user == 0, "expected ns id 0");

    TEST("Create ipc+net namespace");
    int ns_full = tipc_namespace_create(&sec, "ns_full", TNS_TYPE_IPC | TNS_TYPE_NET);
    ASSERT(ns_full == 1, "expected ns id 1");

    TEST("Namespace count is 2");
    ASSERT(sec.ns_count == 2, "expected 2");

    TEST("Enter user namespace");
    ASSERT(tipc_namespace_enter(&sec, ns_user) == TIPC_SEC_OK, "enter failed");

    TEST("User namespace is active");
    ASSERT(sec.namespaces[ns_user].active == 1, "expected active");

    TEST("Leave user namespace");
    ASSERT(tipc_namespace_leave(&sec, ns_user) == TIPC_SEC_OK, "leave failed");

    TEST("User namespace is inactive");
    ASSERT(sec.namespaces[ns_user].active == 0, "expected inactive");

    TEST("Enter invalid namespace");
    ASSERT(tipc_namespace_enter(&sec, 99) == TIPC_SEC_ERR_NAMESPACE,
           "expected ERR_NAMESPACE");
}

/* ======================================================================== */
/*  Test: Capabilities                                                      */
/* ======================================================================== */

static void test_capabilities(void) {
    SECTION("Trit Capabilities");

    tipc_secure_t sec;
    tipc_sec_init(&sec);

    TEST("Grant IPC_LOCK + IPC_SEND to module 0");
    ASSERT(tipc_cap_grant(&sec, "ipc_full", TCAP_IPC_LOCK | TCAP_IPC_SEND, 0) == TIPC_SEC_OK,
           "grant failed");

    TEST("Check module 0 has IPC_SEND");
    ASSERT(tipc_cap_check(&sec, 0, TCAP_IPC_SEND) == 1, "expected has cap");

    TEST("Check module 0 has IPC_LOCK");
    ASSERT(tipc_cap_check(&sec, 0, TCAP_IPC_LOCK) == 1, "expected has cap");

    TEST("Check module 0 does NOT have SYS_ADMIN");
    ASSERT(tipc_cap_check(&sec, 0, TCAP_SYS_ADMIN) == 0, "expected no cap");

    TEST("Check module 1 has no caps (not granted)");
    ASSERT(tipc_cap_check(&sec, 1, TCAP_IPC_SEND) == 0, "expected no cap");

    TEST("Grant NET_RAW to module 1");
    ASSERT(tipc_cap_grant(&sec, "net_raw", TCAP_NET_RAW, 1) == TIPC_SEC_OK,
           "grant failed");

    TEST("Module 1 has NET_RAW");
    ASSERT(tipc_cap_check(&sec, 1, TCAP_NET_RAW) == 1, "expected has cap");
}

/* ======================================================================== */
/*  Test: Injection Attack Detection                                        */
/* ======================================================================== */

static void test_injection(void) {
    SECTION("Injection Attack Detection");

    tipc_secure_t sec;
    tipc_sec_init(&sec);
    tipc_socket_create(&sec, "victim_sock", 0);
    tipc_socket_activate(&sec, 0);

    /* Malicious all-True payload (suspicious pattern) */
    trit malicious[8] = {TRIT_TRUE, TRIT_TRUE, TRIT_TRUE, TRIT_TRUE,
                         TRIT_TRUE, TRIT_TRUE, TRIT_TRUE, TRIT_TRUE};

    TEST("Detect all-True injection (blocked)");
    ASSERT(tipc_inject_simulate(&sec, 0, malicious, 8) == TIPC_SEC_ERR_INJECT,
           "expected INJECT blocked");

    TEST("Inject attempts counter");
    ASSERT(sec.inject_attempts == 1, "expected 1 attempt");

    TEST("Inject blocked counter");
    ASSERT(sec.inject_blocked == 1, "expected 1 blocked");

    /* Normal mixed payload — should pass */
    trit normal[] = {TRIT_TRUE, TRIT_UNKNOWN, TRIT_FALSE};

    TEST("Normal data passes injection check");
    ASSERT(tipc_inject_simulate(&sec, 0, normal, 3) == TIPC_SEC_OK,
           "expected OK for normal data");

    TEST("Inject stats via API");
    ASSERT(tipc_inject_stats(&sec) == 1, "expected 1 blocked total");
}

/* ======================================================================== */
/*  Main                                                                    */
/* ======================================================================== */

int main(void) {
    printf("\n╔══════════════════════════════════════════════════════════════╗\n");
    printf("║  seT6 Secure Inter-Module Communication Test Suite          ║\n");
    printf("╚══════════════════════════════════════════════════════════════╝\n");

    test_init();
    test_sockets();
    test_send_recv();
    test_namespaces();
    test_capabilities();
    test_injection();

    printf("\n══════════════════════════════════════════════════════════════\n");
    printf("  Secure IPC Tests: %d passed, %d failed, %d total\n",
           tests_passed, tests_failed, tests_total);
        printf("=== Results: %d passed, %d failed ===\n",
            tests_passed, tests_failed);
    printf("══════════════════════════════════════════════════════════════\n");

    return tests_failed > 0 ? 1 : 0;
}
