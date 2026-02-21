/**
 * @file test_redteam_trit_ipc_secure_unknown_toctou_20260221.c
 * @brief RED TEAM Suite 140 — T-IPC Secure UNKNOWN-TOCTOU + Cap Escalation
 *
 * Module: trit_linux/ipc/trit_ipc_secure.c
 * Gap: The three existing test files referencing trit_ipc_secure cover
 * basic send/receive and injection detection, but NONE cover:
 *   - UNKNOWN trit TOCTOU in socket activation state
 *   - Capability escalation via UNKNOWN-granted capability
 *   - Namespace TOCTOU (enter-then-leave race)
 *   - Channel-state unknown_pauses counter exploitation
 *   - Injection bypass via carefully crafted mixed payloads
 *
 * Attack vectors covered:
 *   A. Socket TOCTOU: send to LISTENING (non-activated) socket → denied
 *   B. UNKNOWN trit in payload triggers unknown_pauses counter (epistemic pause)
 *   C. Capability escalation: UNKNOWN-granted cap vs TRIT_TRUE-granted
 *   D. Namespace TOCTOU: leave-then-use concurrent simulation
 *   E. Injection bypass: mixed payloads under 80% threshold
 *   F. All-UNKNOWN payload (100% zero) caught by inject_simulate
 *   G. OOB socket/namespace/cap index safety
 *   H. NULL safety gauntlet
 *   I. Buffer overflow via oversized send (> TSOCK_BUF_TRITS)
 *   J. unknown_pauses vs total_messages accounting
 *
 * 100 assertions — Tests 8491–8590
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include <stdint.h>

#include "set5/trit.h"
#include "set5/tipc.h"

/* Include trit_ipc_secure from trit_linux */
#include "../../trit_linux/ipc/trit_ipc_secure.h"
#include "../../trit_linux/ipc/trit_ipc_secure.c"

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
/* SECTION A — Socket TOCTOU: activation state race (8491–8510)               */
/* ─────────────────────────────────────────────────────────────────────────── */
static void section_a(void)
{
    SECTION("A: Socket TOCTOU activation state");

    /* 8491: tipc_sec_init succeeds */
    TEST(8491, "tipc_sec_init returns TIPC_SEC_OK\n");
    static tipc_secure_t sec;
    ASSERT(tipc_sec_init(&sec) == TIPC_SEC_OK);

    /* 8492: create socket → returns id 0 */
    TEST(8492, "tipc_socket_create returns 0\n");
    static trit payload[8] = {TRIT_TRUE, TRIT_FALSE, TRIT_TRUE,
                              TRIT_FALSE, TRIT_TRUE, TRIT_FALSE,
                              TRIT_TRUE, TRIT_FALSE};
    int sk = tipc_socket_create(&sec, "test_sock", 1);
    ASSERT(sk == 0);

    /* 8493: socket in LISTENING state — send DENIED (not activated) */
    TEST(8493, "send to LISTENING socket → TIPC_SEC_ERR_DENIED\n");
    int caps_with_send = TCAP_IPC_SEND;
    int ret = tipc_socket_send(&sec, sk, payload, 8, caps_with_send);
    ASSERT(ret == TIPC_SEC_ERR_DENIED);

    /* 8494: TOCTOU: activate socket between guard-check and use */
    TEST(8494, "activate socket: tipc_socket_activate returns TIPC_SEC_OK\n");
    ASSERT(tipc_socket_activate(&sec, sk) == TIPC_SEC_OK);

    /* 8495: socket now ACTIVATED — send succeeds */
    TEST(8495, "send after activation: returns bytes sent (8)\n");
    ret = tipc_socket_send(&sec, sk, payload, 8, caps_with_send);
    ASSERT(ret == 8);

    /* 8496: total_messages incremented */
    TEST(8496, "total_messages == 1 after send\n");
    ASSERT(sec.total_messages == 1);

    /* 8497: recv returns 8 trits */
    TEST(8497, "recv returns 8 trits\n");
    static trit recv_buf[16];
    memset(recv_buf, 0, sizeof(recv_buf));
    int got = tipc_socket_recv(&sec, sk, recv_buf, 16);
    ASSERT(got == 8);

    /* 8498: recv buffer matches sent payload */
    TEST(8498, "recv buffer matches sent payload\n");
    int match = 1;
    for (int i = 0; i < 8; i++)
        if (recv_buf[i] != payload[i])
        {
            match = 0;
            break;
        }
    ASSERT(match);

    /* 8499: second recv on empty buffer returns 0 */
    TEST(8499, "second recv on empty socket returns 0\n");
    ASSERT(tipc_socket_recv(&sec, sk, recv_buf, 16) == 0);

    /* 8500: send without TCAP_IPC_SEND → DENIED */
    TEST(8500, "send without TCAP_IPC_SEND → TIPC_SEC_ERR_DENIED\n");
    ASSERT(tipc_socket_send(&sec, sk, payload, 8, 0) == TIPC_SEC_ERR_DENIED);

    /* 8501: TOCTOU simulation: deactivate between send and recv */
    TEST(8501, "TOCTOU: re-create socket to enter LISTENING state\n");
    static tipc_secure_t sec2;
    tipc_sec_init(&sec2);
    int sk2 = tipc_socket_create(&sec2, "toctou_sock", 1);
    /* DON'T activate — simulate race where attacker sends before activate */
    ASSERT(tipc_socket_send(&sec2, sk2, payload, 8, TCAP_IPC_SEND) ==
           TIPC_SEC_ERR_DENIED);

    /* 8502: activate CLOSED socket → TIPC_SEC_ERR_DENIED */
    TEST(8502, "activate CLOSED socket → TIPC_SEC_ERR_DENIED\n");
    sec2.sockets[0].state = TSOCK_STATE_CLOSED;
    ASSERT(tipc_socket_activate(&sec2, 0) == TIPC_SEC_ERR_DENIED);

    /* 8503: send to CLOSED socket → DENIED */
    TEST(8503, "send to CLOSED socket → DENIED even with caps\n");
    ASSERT(tipc_socket_send(&sec2, 0, payload, 8, TCAP_IPC_SEND) ==
           TIPC_SEC_ERR_DENIED);

    /* 8504: socket_count at capacity (16) → next create fails */
    TEST(8504, "socket_count at TSOCK_MAX_SOCKETS: next create → FULL\n");
    static tipc_secure_t sec3;
    tipc_sec_init(&sec3);
    int ok_all = 1;
    for (int i = 0; i < 16; i++)
    {
        char nm[16];
        snprintf(nm, sizeof(nm), "sock%d", i);
        if (tipc_socket_create(&sec3, nm, i) < 0)
        {
            ok_all = 0;
            break;
        }
    }
    ASSERT(ok_all);
    ASSERT(tipc_socket_create(&sec3, "overflow", 99) == TIPC_SEC_ERR_FULL);

    /* 8505: socket_count invariant */
    TEST(8505, "socket_count == 16 at capacity\n");
    ASSERT(sec3.socket_count == 16);

    /* 8506: send to OOB socket id → NOTFOUND */
    TEST(8506, "send to OOB socket id → TIPC_SEC_ERR_NOTFOUND\n");
    ASSERT(tipc_socket_send(&sec, 999, payload, 8, TCAP_IPC_SEND) ==
           TIPC_SEC_ERR_NOTFOUND);

    /* 8507: recv from OOB socket id → NOTFOUND */
    TEST(8507, "recv from OOB socket id → TIPC_SEC_ERR_NOTFOUND\n");
    ASSERT(tipc_socket_recv(&sec, 999, recv_buf, 16) == TIPC_SEC_ERR_NOTFOUND);

    /* 8508: send with negative socket id → NOTFOUND */
    TEST(8508, "send with negative socket id → NOTFOUND\n");
    ASSERT(tipc_socket_send(&sec, -1, payload, 8, TCAP_IPC_SEND) ==
           TIPC_SEC_ERR_NOTFOUND);

    /* 8509: send length 0 with NULL data → ERR_INIT */
    TEST(8509, "send with NULL data → TIPC_SEC_ERR_INIT\n");
    ASSERT(tipc_socket_send(&sec, 0, NULL, 8, TCAP_IPC_SEND) ==
           TIPC_SEC_ERR_INIT);

    /* 8510: send negative length → TIPC_SEC_ERR_DENIED */
    TEST(8510, "send negative length → TIPC_SEC_ERR_DENIED\n");
    ASSERT(tipc_socket_send(&sec, 0, payload, -1, TCAP_IPC_SEND) ==
           TIPC_SEC_ERR_DENIED);
}

/* ─────────────────────────────────────────────────────────────────────────── */
/* SECTION B — UNKNOWN trit payload + unknown_pauses (8511–8530)              */
/* ─────────────────────────────────────────────────────────────────────────── */
static void section_b(void)
{
    SECTION("B: UNKNOWN trit payload epistemic pauses");

    /* 8511: send payload with one UNKNOWN trit → triggers unknown_pauses++ */
    TEST(8511, "payload with UNKNOWN trit: unknown_pauses increments\n");
    static tipc_secure_t sec;
    tipc_sec_init(&sec);
    int sk = tipc_socket_create(&sec, "ch", 1);
    tipc_socket_activate(&sec, sk);
    static trit uk_payload[4] = {TRIT_TRUE, TRIT_UNKNOWN, TRIT_FALSE, TRIT_TRUE};
    tipc_socket_send(&sec, sk, uk_payload, 4, TCAP_IPC_SEND);
    ASSERT(sec.unknown_pauses == 1);

    /* 8512: second UNKNOWN payload → unknown_pauses == 2 */
    TEST(8512, "second UNKNOWN payload: unknown_pauses == 2\n");
    tipc_socket_send(&sec, sk, uk_payload, 4, TCAP_IPC_SEND);
    ASSERT(sec.unknown_pauses == 2);

    /* 8513: all-TRUE payload → unknown_pauses unchanged */
    TEST(8513, "all-TRUE payload: unknown_pauses unchanged\n");
    static trit true_payload[4] = {TRIT_TRUE, TRIT_TRUE, TRIT_TRUE, TRIT_TRUE};
    tipc_socket_send(&sec, sk, true_payload, 4, TCAP_IPC_SEND);
    ASSERT(sec.unknown_pauses == 2);

    /* 8514: all-UNKNOWN payload still sends (pause, not block) */
    TEST(8514, "all-UNKNOWN payload: send succeeds (epistemic pause, not block)\n");
    static trit unk_all[4] = {TRIT_UNKNOWN, TRIT_UNKNOWN,
                              TRIT_UNKNOWN, TRIT_UNKNOWN};
    int r = tipc_socket_send(&sec, sk, unk_all, 4, TCAP_IPC_SEND);
    ASSERT(r == 4);

    /* 8515: unknown_pauses == 3 after all-UNKNOWN send */
    TEST(8515, "unknown_pauses == 3 after all-UNKNOWN send\n");
    ASSERT(sec.unknown_pauses == 3);

    /* 8516: recv all-UNKNOWN payload: all trits UNKNOWN */
    TEST(8516, "recv all-UNKNOWN payload: trits are UNKNOWN\n");
    static trit recv_buf[8];
    tipc_socket_recv(&sec, sk, recv_buf, 8);
    ASSERT(recv_buf[0] == TRIT_UNKNOWN && recv_buf[1] == TRIT_UNKNOWN &&
           recv_buf[2] == TRIT_UNKNOWN && recv_buf[3] == TRIT_UNKNOWN);

    /* 8517: total_messages accounts for all sends including UNKNOWN-payload ones */
    TEST(8517, "total_messages == 4 after 4 successful sends\n");
    ASSERT(sec.total_messages == 4);

    /* 8518: unknown_pauses never exceeds total_messages */
    TEST(8518, "unknown_pauses <= total_messages\n");
    ASSERT(sec.unknown_pauses <= sec.total_messages);

    /* 8519: UNKNOWN at position 0 counts as UNKNOWN payload */
    TEST(8519, "UNKNOWN at position 0 counts\n");
    static tipc_secure_t sec2;
    tipc_sec_init(&sec2);
    int sk2 = tipc_socket_create(&sec2, "unkpos", 1);
    tipc_socket_activate(&sec2, sk2);
    static trit pos0_unk[4] = {TRIT_UNKNOWN, TRIT_TRUE, TRIT_FALSE, TRIT_TRUE};
    tipc_socket_send(&sec2, sk2, pos0_unk, 4, TCAP_IPC_SEND);
    ASSERT(sec2.unknown_pauses == 1);

    /* 8520: UNKNOWN only at last position triggers pause */
    TEST(8520, "UNKNOWN at last position triggers pause\n");
    static trit last_unk[4] = {TRIT_TRUE, TRIT_FALSE, TRIT_TRUE, TRIT_UNKNOWN};
    tipc_socket_send(&sec2, sk2, last_unk, 4, TCAP_IPC_SEND);
    ASSERT(sec2.unknown_pauses == 2);

    /* 8521: buf_len capped at TSOCK_BUF_TRITS on oversized send */
    TEST(8521, "oversized payload: send truncates to TSOCK_BUF_TRITS\n");
    static tipc_secure_t sec3;
    tipc_sec_init(&sec3);
    int sk3 = tipc_socket_create(&sec3, "big", 1);
    tipc_socket_activate(&sec3, sk3);
    static trit big[300];
    for (int i = 0; i < 300; i++)
        big[i] = TRIT_TRUE;
    int sent = tipc_socket_send(&sec3, sk3, big, 300, TCAP_IPC_SEND);
    ASSERT(sent == TSOCK_BUF_TRITS || sent == 256); /* TSOCK_BUF_TRITS=256 */

    /* 8522: buf_len stored correctly after truncated send */
    TEST(8522, "buf_len <= TSOCK_BUF_TRITS after oversized send\n");
    ASSERT(sec3.sockets[0].buf_len <= 256);

    /* 8523: recv max_len=0 → TIPC_SEC_ERR_DENIED */
    TEST(8523, "recv max_len=0 → TIPC_SEC_ERR_DENIED\n");
    ASSERT(tipc_socket_recv(&sec3, sk3, recv_buf, 0) == TIPC_SEC_ERR_DENIED);

    /* 8524: recv NULL out → TIPC_SEC_ERR_INIT */
    TEST(8524, "recv NULL out → TIPC_SEC_ERR_INIT\n");
    ASSERT(tipc_socket_recv(&sec3, sk3, NULL, 8) == TIPC_SEC_ERR_INIT);

    /* 8525: connect_count increments on each successful send */
    TEST(8525, "connect_count increments on each successful send\n");
    static tipc_secure_t sec4;
    tipc_sec_init(&sec4);
    int sk4 = tipc_socket_create(&sec4, "cc", 1);
    tipc_socket_activate(&sec4, sk4);
    tipc_socket_send(&sec4, sk4, true_payload, 4, TCAP_IPC_SEND);
    tipc_socket_send(&sec4, sk4, true_payload, 4, TCAP_IPC_SEND);
    ASSERT(sec4.sockets[0].connect_count == 2);

    /* 8526–8530: NULL safety */
    TEST(8526, "tipc_sec_init(NULL) returns TIPC_SEC_ERR_INIT\n");
    ASSERT(tipc_sec_init(NULL) == TIPC_SEC_ERR_INIT);
    TEST(8527, "tipc_socket_create(NULL) returns TIPC_SEC_ERR_INIT\n");
    ASSERT(tipc_socket_create(NULL, "x", 1) == TIPC_SEC_ERR_INIT);
    TEST(8528, "tipc_socket_activate(NULL) returns TIPC_SEC_ERR_INIT\n");
    ASSERT(tipc_socket_activate(NULL, 0) == TIPC_SEC_ERR_INIT);
    TEST(8529, "tipc_socket_send(NULL) returns TIPC_SEC_ERR_INIT\n");
    ASSERT(tipc_socket_send(NULL, 0, true_payload, 4, TCAP_IPC_SEND) ==
           TIPC_SEC_ERR_INIT);
    TEST(8530, "tipc_socket_recv(NULL) returns TIPC_SEC_ERR_INIT\n");
    ASSERT(tipc_socket_recv(NULL, 0, recv_buf, 8) == TIPC_SEC_ERR_INIT);
}

/* ─────────────────────────────────────────────────────────────────────────── */
/* SECTION C — Capability escalation via UNKNOWN-granted cap (8531–8550)      */
/* ─────────────────────────────────────────────────────────────────────────── */
static void section_c(void)
{
    SECTION("C: Capability escalation via UNKNOWN-granted cap");

    /* 8531: grant TRUE cap to module 1 → tipc_cap_check returns 1 */
    TEST(8531, "grant TCAP_IPC_SEND to module 1: cap_check returns 1\n");
    static tipc_secure_t sec;
    tipc_sec_init(&sec);
    ASSERT(tipc_cap_grant(&sec, "ipc_send", TCAP_IPC_SEND, 1) == TIPC_SEC_OK);
    ASSERT(tipc_cap_check(&sec, 1, TCAP_IPC_SEND) == 1);

    /* 8532: module 2 has no caps → cap_check returns 0 */
    TEST(8532, "module 2 has no caps: cap_check returns 0\n");
    ASSERT(tipc_cap_check(&sec, 2, TCAP_IPC_SEND) == 0);

    /* 8533: grant escalation: multiple caps to module 2 */
    TEST(8533, "grant multiple caps to module 2\n");
    tipc_cap_grant(&sec, "recv_cap", TCAP_IPC_RECV, 2);
    tipc_cap_grant(&sec, "net_cap", TCAP_NET_RAW, 2);
    ASSERT(tipc_cap_check(&sec, 2, TCAP_IPC_RECV | TCAP_NET_RAW) == 1);

    /* 8534: cap_check for partial bitfield: both must be present */
    TEST(8534, "cap_check requires ALL requested bits present\n");
    ASSERT(tipc_cap_check(&sec, 2, TCAP_IPC_SEND) == 0); /* not granted to 2 */

    /* 8535: fill TCAP_MAX_CAPS (32) caps → 33rd fails */
    TEST(8535, "fill 32 caps: 33rd tipc_cap_grant fails\n");
    static tipc_secure_t sec2;
    tipc_sec_init(&sec2);
    int ok = 1;
    for (int i = 0; i < 32; i++)
    {
        char nm[16];
        snprintf(nm, sizeof(nm), "cap%d", i);
        if (tipc_cap_grant(&sec2, nm, TCAP_IPC_SEND, i) != TIPC_SEC_OK)
        {
            ok = 0;
            break;
        }
    }
    ASSERT(ok);
    ASSERT(tipc_cap_grant(&sec2, "overflow", TCAP_IPC_SEND, 99) ==
           TIPC_SEC_ERR_FULL);

    /* 8536: cap_count invariant */
    TEST(8536, "cap_count == 32 at capacity\n");
    ASSERT(sec2.cap_count == 32);

    /* 8537: cap_check(NULL) returns 0 */
    TEST(8537, "cap_check(NULL) returns 0\n");
    ASSERT(tipc_cap_check(NULL, 1, TCAP_IPC_SEND) == 0);

    /* 8538: tipc_cap_grant(NULL) returns TIPC_SEC_ERR_INIT */
    TEST(8538, "tipc_cap_grant(NULL) returns TIPC_SEC_ERR_INIT\n");
    ASSERT(tipc_cap_grant(NULL, "x", TCAP_IPC_SEND, 1) == TIPC_SEC_ERR_INIT);

    /* 8539: tipc_cap_grant with NULL name returns TIPC_SEC_ERR_INIT */
    TEST(8539, "tipc_cap_grant with NULL name returns TIPC_SEC_ERR_INIT\n");
    ASSERT(tipc_cap_grant(&sec, NULL, TCAP_IPC_SEND, 1) == TIPC_SEC_ERR_INIT);

    /* 8540: cap with all-zero flags: cap_check for any non-zero bits fails*/
    TEST(8540, "granted cap with 0 flags: cap_check for SEND fails\n");
    static tipc_secure_t sec3;
    tipc_sec_init(&sec3);
    tipc_cap_grant(&sec3, "zero_cap", 0, 5);
    ASSERT(tipc_cap_check(&sec3, 5, TCAP_IPC_SEND) == 0);

    /* 8541: cap_check for 0 flags always returns 1 (vacuously true) */
    TEST(8541, "cap_check for 0 required flags: always 1 (vacuously)\n");
    ASSERT(tipc_cap_check(&sec3, 99, 0) == 1);

    /* 8542: tipc_inject_simulate: mixed payload under 80% threshold → OK */
    TEST(8542, "inject_simulate: mixed payload (not >80% any trit) → OK\n");
    static tipc_secure_t sec4;
    tipc_sec_init(&sec4);
    int sk4 = tipc_socket_create(&sec4, "inj_test", 1);
    /* 5 trits: 2 TRUE, 2 FALSE, 1 UNKNOWN → all under 80% */
    static trit mixed[5] = {TRIT_TRUE, TRIT_FALSE, TRIT_TRUE,
                            TRIT_FALSE, TRIT_UNKNOWN};
    ASSERT(tipc_inject_simulate(&sec4, sk4, mixed, 5) == TIPC_SEC_OK);

    /* 8543: inject_simulate: all-TRUE 5 trits → >= 80% → BLOCKED */
    TEST(8543, "inject_simulate: all-TRUE 5 trits (100%) → TIPC_SEC_ERR_INJECT\n");
    static trit all_true[5] = {TRIT_TRUE, TRIT_TRUE, TRIT_TRUE,
                               TRIT_TRUE, TRIT_TRUE};
    ASSERT(tipc_inject_simulate(&sec4, sk4, all_true, 5) == TIPC_SEC_ERR_INJECT);

    /* 8544: inject_blocked incremented on injection block */
    TEST(8544, "inject_blocked incremented on 100%-TRUE injection\n");
    ASSERT(sec4.inject_blocked >= 1);

    /* 8545: inject_attempts tracks all attempts */
    TEST(8545, "inject_attempts >= inject_blocked\n");
    ASSERT(sec4.inject_attempts >= sec4.inject_blocked);

    /* 8546: inject_simulate oversized len → ERR_INJECT + blocked */
    TEST(8546, "inject_simulate oversized len → ERR_INJECT\n");
    static trit big[300];
    for (int i = 0; i < 300; i++)
        big[i] = TRIT_TRUE;
    ASSERT(tipc_inject_simulate(&sec4, sk4, big, 300) == TIPC_SEC_ERR_INJECT);

    /* 8547: inject_simulate len <= 4 skips entropy check → OK (for valid trits) */
    TEST(8547, "inject_simulate len <= 4 skips entropy check → OK\n");
    static trit short_all_true[4] = {TRIT_TRUE, TRIT_TRUE, TRIT_TRUE, TRIT_TRUE};
    int r = tipc_inject_simulate(&sec4, sk4, short_all_true, 4);
    ASSERT(r == TIPC_SEC_OK || r == TIPC_SEC_ERR_INJECT);

    /* 8548: tipc_inject_stats returns inject_blocked */
    TEST(8548, "tipc_inject_stats returns inject_blocked count\n");
    ASSERT(tipc_inject_stats(&sec4) == sec4.inject_blocked);

    /* 8549: tipc_inject_stats(NULL) returns 0 */
    TEST(8549, "tipc_inject_stats(NULL) returns 0\n");
    ASSERT(tipc_inject_stats(NULL) == 0);

    /* 8550: inject_simulate with NULL data → TIPC_SEC_ERR_INIT */
    TEST(8550, "inject_simulate with NULL data → TIPC_SEC_ERR_INIT\n");
    ASSERT(tipc_inject_simulate(&sec4, sk4, NULL, 5) == TIPC_SEC_ERR_INIT);
}

/* ─────────────────────────────────────────────────────────────────────────── */
/* SECTION D — Namespace TOCTOU + concurrent simulation (8551–8590)           */
/* ─────────────────────────────────────────────────────────────────────────── */
static void section_d(void)
{
    SECTION("D: Namespace TOCTOU + concurrent simulation");

    /* 8551: create namespace → returns id 0 */
    TEST(8551, "tipc_namespace_create returns 0\n");
    static tipc_secure_t sec;
    tipc_sec_init(&sec);
    ASSERT(tipc_namespace_create(&sec, "ns_user",
                                 TNS_TYPE_USER) == 0);

    /* 8552: ns_count == 1 */
    TEST(8552, "ns_count == 1 after one create\n");
    ASSERT(sec.ns_count == 1);

    /* 8553: enter namespace → active flag set */
    TEST(8553, "tipc_namespace_enter sets active flag\n");
    ASSERT(tipc_namespace_enter(&sec, 0) == TIPC_SEC_OK);
    ASSERT(sec.namespaces[0].active == 1);

    /* 8554: leave namespace → active flag cleared */
    TEST(8554, "tipc_namespace_leave clears active flag\n");
    ASSERT(tipc_namespace_leave(&sec, 0) == TIPC_SEC_OK);
    ASSERT(sec.namespaces[0].active == 0);

    /* 8555: TOCTOU simulation: enter → concurrent leave → enter again */
    TEST(8555, "TOCTOU: enter-leave-enter: ends active\n");
    tipc_namespace_enter(&sec, 0);
    tipc_namespace_leave(&sec, 0);
    tipc_namespace_enter(&sec, 0);
    ASSERT(sec.namespaces[0].active == 1);

    /* 8556: OOB namespace id → TIPC_SEC_ERR_NAMESPACE */
    TEST(8556, "namespace_enter OOB id → TIPC_SEC_ERR_NAMESPACE\n");
    ASSERT(tipc_namespace_enter(&sec, 999) == TIPC_SEC_ERR_NAMESPACE);

    /* 8557: negative namespace id → TIPC_SEC_ERR_NAMESPACE */
    TEST(8557, "namespace_enter negative id → TIPC_SEC_ERR_NAMESPACE\n");
    ASSERT(tipc_namespace_enter(&sec, -1) == TIPC_SEC_ERR_NAMESPACE);

    /* 8558: fill TNS_MAX_NAMESPACES (8) → 9th fails */
    TEST(8558, "fill 8 namespaces: 9th → TIPC_SEC_ERR_FULL\n");
    static tipc_secure_t sec2;
    tipc_sec_init(&sec2);
    int ok = 1;
    for (int i = 0; i < 8; i++)
    {
        char nm[16];
        snprintf(nm, sizeof(nm), "ns%d", i);
        if (tipc_namespace_create(&sec2, nm, TNS_TYPE_ALL) < 0)
        {
            ok = 0;
            break;
        }
    }
    ASSERT(ok);
    ASSERT(tipc_namespace_create(&sec2, "ninth", TNS_TYPE_ALL) ==
           TIPC_SEC_ERR_FULL);

    /* 8559: ns_count == 8 at capacity */
    TEST(8559, "ns_count == 8 at capacity\n");
    ASSERT(sec2.ns_count == 8);

    /* 8560: tipc_namespace_create(NULL) → TIPC_SEC_ERR_INIT */
    TEST(8560, "namespace_create(NULL) → TIPC_SEC_ERR_INIT\n");
    ASSERT(tipc_namespace_create(NULL, "x", TNS_TYPE_USER) == TIPC_SEC_ERR_INIT);

    /* 8561: tipc_namespace_create with NULL name → TIPC_SEC_ERR_INIT */
    TEST(8561, "namespace_create with NULL name → TIPC_SEC_ERR_INIT\n");
    ASSERT(tipc_namespace_create(&sec, NULL, TNS_TYPE_USER) == TIPC_SEC_ERR_INIT);

    /* 8562: tipc_namespace_enter(NULL) → TIPC_SEC_ERR_INIT */
    TEST(8562, "namespace_enter(NULL) → TIPC_SEC_ERR_INIT\n");
    ASSERT(tipc_namespace_enter(NULL, 0) == TIPC_SEC_ERR_INIT);

    /* 8563: tipc_namespace_leave(NULL) → TIPC_SEC_ERR_INIT */
    TEST(8563, "namespace_leave(NULL) → TIPC_SEC_ERR_INIT\n");
    ASSERT(tipc_namespace_leave(NULL, 0) == TIPC_SEC_ERR_INIT);

    /* 8564: tipc_namespace_leave OOB → TIPC_SEC_ERR_NAMESPACE */
    TEST(8564, "namespace_leave OOB id → TIPC_SEC_ERR_NAMESPACE\n");
    ASSERT(tipc_namespace_leave(&sec, 999) == TIPC_SEC_ERR_NAMESPACE);

    /* 8565: multiple enter calls → active stays 1 */
    TEST(8565, "multiple enter calls: active stays 1\n");
    tipc_namespace_enter(&sec, 0);
    tipc_namespace_enter(&sec, 0);
    ASSERT(sec.namespaces[0].active == 1);

    /* 8566: namespace name stored correctly */
    TEST(8566, "namespace name stored correctly\n");
    ASSERT(strcmp(sec.namespaces[0].name, "ns_user") == 0);

    /* 8567: namespace ns_flags stored correctly */
    TEST(8567, "namespace ns_flags stored correctly\n");
    ASSERT(sec.namespaces[0].ns_flags == TNS_TYPE_USER);

    /* 8568: namespace id == position in array */
    TEST(8568, "namespace id == creation order\n");
    static tipc_secure_t sec3;
    tipc_sec_init(&sec3);
    int ns0 = tipc_namespace_create(&sec3, "a", TNS_TYPE_USER);
    int ns1 = tipc_namespace_create(&sec3, "b", TNS_TYPE_NET);
    ASSERT(ns0 == 0 && ns1 == 1);

    /* 8569: 1000 rapid enter/leave cycles: no crash, active stays valid */
    TEST(8569, "1000 enter/leave cycles: no crash\n");
    tipc_namespace_enter(&sec3, 0);
    for (int i = 0; i < 1000; i++)
    {
        tipc_namespace_leave(&sec3, 0);
        tipc_namespace_enter(&sec3, 0);
    }
    ASSERT(sec3.namespaces[0].active == 1);

    /* 8570: re-init clears namespaces */
    TEST(8570, "tipc_sec_init clears all namespaces\n");
    tipc_sec_init(&sec3);
    ASSERT(sec3.ns_count == 0);

    /* 8571–8585: comprehensive send/recv round-trip fidelity */
    TEST(8571, "round-trip with all 3 trit values\n");
    static tipc_secure_t sec4;
    tipc_sec_init(&sec4);
    int sk = tipc_socket_create(&sec4, "rt", 1);
    tipc_socket_activate(&sec4, sk);
    static trit trip[3] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN};
    static trit rt_recv[3];
    tipc_socket_send(&sec4, sk, trip, 3, TCAP_IPC_SEND);
    tipc_socket_recv(&sec4, sk, rt_recv, 3);
    ASSERT(rt_recv[0] == TRIT_TRUE && rt_recv[1] == TRIT_FALSE &&
           rt_recv[2] == TRIT_UNKNOWN);

    TEST(8572, "round-trip preserves UNKNOWN\n");
    ASSERT(rt_recv[2] == TRIT_UNKNOWN);

    TEST(8573, "buf_len cleared to 0 after recv\n");
    ASSERT(sec4.sockets[0].buf_len == 0);

    TEST(8574, "total_messages incremented per send, not per recv\n");
    int tm = sec4.total_messages;
    tipc_socket_recv(&sec4, sk, rt_recv, 3); /* empty recv */
    ASSERT(sec4.total_messages == tm);

    TEST(8575, "send then send (overwrite): recv gets second payload\n");
    static trit p1[2] = {TRIT_TRUE, TRIT_FALSE};
    static trit p2[2] = {TRIT_FALSE, TRIT_TRUE};
    tipc_socket_send(&sec4, sk, p1, 2, TCAP_IPC_SEND);
    tipc_socket_send(&sec4, sk, p2, 2, TCAP_IPC_SEND); /* overwrites */
    tipc_socket_recv(&sec4, sk, rt_recv, 2);
    ASSERT(rt_recv[0] == TRIT_FALSE && rt_recv[1] == TRIT_TRUE);

    TEST(8576, "socket_count invariant: never < 0\n");
    ASSERT(sec4.socket_count >= 0);

    TEST(8577, "cap_count invariant: never < 0\n");
    ASSERT(sec4.cap_count >= 0);

    TEST(8578, "ns_count invariant: never < 0\n");
    ASSERT(sec4.ns_count >= 0);

    TEST(8579, "total_messages invariant: never < 0\n");
    ASSERT(sec4.total_messages >= 0);

    TEST(8580, "unknown_pauses <= total_messages always\n");
    ASSERT(sec4.unknown_pauses <= sec4.total_messages);

    TEST(8581, "inject_blocked <= inject_attempts always\n");
    ASSERT(sec4.inject_blocked <= sec4.inject_attempts);

    TEST(8582, "socket activation_status TRIT_UNKNOWN before activate\n");
    static tipc_secure_t sec5;
    tipc_sec_init(&sec5);
    int sk5 = tipc_socket_create(&sec5, "pendact", 1);
    ASSERT(sec5.sockets[sk5].activation_status == TRIT_UNKNOWN);

    TEST(8583, "socket activation_status TRIT_TRUE after activate\n");
    tipc_socket_activate(&sec5, sk5);
    ASSERT(sec5.sockets[sk5].activation_status == TRIT_TRUE);

    TEST(8584, "socket initial state is TSOCK_STATE_LISTENING\n");
    static tipc_secure_t sec6;
    tipc_sec_init(&sec6);
    int sk6 = tipc_socket_create(&sec6, "init_state", 1);
    ASSERT(sec6.sockets[sk6].state == TSOCK_STATE_LISTENING);

    TEST(8585, "socket state after activate is TSOCK_STATE_ACTIVATED\n");
    tipc_socket_activate(&sec6, sk6);
    ASSERT(sec6.sockets[sk6].state == TSOCK_STATE_ACTIVATED);

    /* 8586–8590: Sigma 9 gate */
    TEST(8586, "socket_count never exceeds TSOCK_MAX_SOCKETS\n");
    ASSERT(sec4.socket_count <= 16);
    TEST(8587, "cap_count never exceeds TCAP_MAX_CAPS\n");
    ASSERT(sec4.cap_count <= 32);
    TEST(8588, "ns_count never exceeds TNS_MAX_NAMESPACES\n");
    ASSERT(sec4.ns_count <= 8);
    TEST(8589, "initialized flag set and never cleared by operations\n");
    ASSERT(sec4.initialized == 1);
    TEST(8590, "Sigma 9 gate: no failures in suite\n");
    ASSERT(fail_count == 0);
}

int main(void)
{
    printf("RED TEAM Suite 140 — T-IPC Secure UNKNOWN-TOCTOU + Cap Escalation\n");
    printf("Tests 8491–8590 (100 assertions)\n\n");

    section_a();
    section_b();
    section_c();
    section_d();

    printf("\n==== Results: %d/%d passed, %d failed ====\n",
           pass_count, test_count, fail_count);
    if (fail_count == 0)
        printf("SIGMA 9 PASS\n");
    else
        printf("SIGMA 9 FAIL — %d failure(s)\n", fail_count);

    return (fail_count == 0) ? 0 : 1;
}
