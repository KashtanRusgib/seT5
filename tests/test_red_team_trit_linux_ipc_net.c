/**
 * @file test_red_team_trit_linux_ipc_net.c
 * @brief Red-team exploit suite for Trit Linux IPC + networking modules.
 *
 * Focus:
 *   - Negative/overflow length abuse
 *   - Invalid trit payload injection
 *   - Malformed packet header tampering
 *   - Queue and checksum abuse paths
 */

#include <stdio.h>
#include <string.h>

#include "set5/trit.h"
#include "set5/trit_net.h"
#include "../trit_linux/ipc/trit_ipc_secure.h"

static int tests_passed = 0;
static int tests_failed = 0;
static int tests_total = 0;

#define TEST(name)               \
    do                           \
    {                            \
        tests_total++;           \
        printf("  %-62s", name); \
    } while (0)

#define PASS()              \
    do                      \
    {                       \
        tests_passed++;     \
        printf("[PASS]\n"); \
    } while (0)

#define FAIL(msg)                   \
    do                              \
    {                               \
        tests_failed++;             \
        printf("[FAIL] %s\n", msg); \
    } while (0)

#define ASSERT(cond, msg) \
    do                    \
    {                     \
        if (cond)         \
        {                 \
            PASS();       \
        }                 \
        else              \
        {                 \
            FAIL(msg);    \
        }                 \
    } while (0)

#define SECTION(name) printf("\nSection: %s\n", name)

static void test_secure_ipc_redteam(void)
{
    SECTION("Secure IPC Exploit Paths");

    tipc_secure_t sec;
    tipc_sec_init(&sec);

    int sid = tipc_socket_create(&sec, "rt_sock", 0);
    tipc_socket_activate(&sec, sid);

    trit payload[4] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
    trit out[8] = {0};

    TEST("IPC send: negative length is denied");
    ASSERT(tipc_socket_send(&sec, sid, payload, -1, TCAP_IPC_SEND) == TIPC_SEC_ERR_DENIED,
           "negative len accepted");

    TEST("IPC recv: zero max_len is denied");
    ASSERT(tipc_socket_recv(&sec, sid, out, 0) == TIPC_SEC_ERR_DENIED,
           "zero max_len accepted");

    TEST("IPC recv: negative max_len is denied");
    ASSERT(tipc_socket_recv(&sec, sid, out, -7) == TIPC_SEC_ERR_DENIED,
           "negative max_len accepted");

    TEST("Injection simulate: NULL payload rejected");
    ASSERT(tipc_inject_simulate(&sec, sid, NULL, 4) == TIPC_SEC_ERR_INIT,
           "NULL payload accepted");

    TEST("Injection simulate: negative length blocked");
    ASSERT(tipc_inject_simulate(&sec, sid, payload, -3) == TIPC_SEC_ERR_INJECT,
           "negative injection len accepted");

    TEST("Injection simulate: zero length blocked");
    ASSERT(tipc_inject_simulate(&sec, sid, payload, 0) == TIPC_SEC_ERR_INJECT,
           "zero injection len accepted");

    TEST("Injection simulate: oversized length blocked");
    ASSERT(tipc_inject_simulate(&sec, sid, payload, TSOCK_BUF_TRITS + 1) == TIPC_SEC_ERR_INJECT,
           "oversized injection len accepted");

    trit invalid_payload[5] = {TRIT_TRUE, TRIT_FALSE, (trit)7, TRIT_UNKNOWN, TRIT_TRUE};
    TEST("Injection simulate: out-of-range trit blocked");
    ASSERT(tipc_inject_simulate(&sec, sid, invalid_payload, 5) == TIPC_SEC_ERR_INJECT,
           "invalid trit accepted");

    trit mixed_payload[6] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN};
    TEST("Injection simulate: mixed payload accepted");
    ASSERT(tipc_inject_simulate(&sec, sid, mixed_payload, 6) == TIPC_SEC_OK,
           "mixed payload blocked");

    TEST("Injection counters: attempts tracked");
       ASSERT(sec.inject_attempts == 5, "unexpected inject_attempts count");

    TEST("Injection counters: blocked tracked");
    ASSERT(sec.inject_blocked == 4, "unexpected inject_blocked count");
}

static void test_tnet_redteam(void)
{
    SECTION("T-Net Exploit Paths");

    tnet_stack_t stack;
    tnet_addr_t local;
    tnet_addr_from_int(&local, 101);
    tnet_init(&stack, &local);

    tnet_addr_t dst;
    tnet_addr_from_int(&dst, 101);

    trit payload[4] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
    tnet_packet_t pkt;

    TEST("Build packet: negative length rejected");
    ASSERT(tnet_build_packet(&pkt, &local, &dst, NULL, NULL, TNET_PROTO_DATA, payload, -1) == TNET_ERR_INIT,
           "negative len accepted");

    trit bad_payload[3] = {TRIT_TRUE, (trit)9, TRIT_FALSE};
    TEST("Build packet: invalid trit payload rejected");
    ASSERT(tnet_build_packet(&pkt, &local, &dst, NULL, NULL, TNET_PROTO_DATA, bad_payload, 3) == TNET_ERR_BADADDR,
           "invalid trit accepted");

    TEST("Send: negative length rejected");
    ASSERT(tnet_send(&stack, &dst, NULL, TNET_PROTO_DATA, payload, -2) == TNET_ERR_INIT,
           "negative send len accepted");

    TEST("Send: oversized length rejected");
    ASSERT(tnet_send(&stack, &dst, NULL, TNET_PROTO_DATA, payload, TNET_MAX_PAYLOAD + 4) == TNET_ERR_INIT,
           "oversized send len accepted");

    TEST("Send: NULL payload with nonzero len rejected");
    ASSERT(tnet_send(&stack, &dst, NULL, TNET_PROTO_DATA, NULL, 3) == TNET_ERR_INIT,
           "NULL payload accepted");

    TEST("Send: valid payload accepted");
    ASSERT(tnet_send(&stack, &dst, NULL, TNET_PROTO_DATA, payload, 4) == TNET_OK,
           "valid send failed");

    TEST("Loopback: valid packet delivered");
    ASSERT(tnet_loopback(&stack) == 1, "expected one looped packet");

    tnet_packet_t rx;
    TEST("Recv: receives looped packet");
    ASSERT(tnet_recv(&stack, &rx) == TNET_OK, "recv failed");

    TEST("Checksum verify: forged negative payload_len rejected");
    {
        tnet_packet_t forged;
        memset(&forged, 0, sizeof(forged));
        forged.header.payload_len = -1;
        ASSERT(tnet_checksum_verify(&forged) == 0, "negative payload_len accepted");
    }

    TEST("Checksum verify: forged oversized payload_len rejected");
    {
        tnet_packet_t forged;
        memset(&forged, 0, sizeof(forged));
        forged.header.payload_len = TNET_MAX_PAYLOAD + 1;
        ASSERT(tnet_checksum_verify(&forged) == 0, "oversized payload_len accepted");
    }

    TEST("Loopback: tampered TX header length is dropped");
    {
              int prep = tnet_send(&stack, &dst, NULL, TNET_PROTO_DATA, payload, 4);
              if (prep != TNET_OK) {
                     FAIL("prep send failed");
                     return;
              }
        stack.tx_queue[stack.tx_head].header.payload_len = TNET_MAX_PAYLOAD + 9;
        int before_errors = stack.checksum_errors;
        int looped = tnet_loopback(&stack);
        ASSERT(looped == 0 && stack.checksum_errors == before_errors + 1,
               "tampered packet not dropped");
    }
}

int main(void)
{
    printf("==============================================\n");
    printf("  Red-Team Trit Linux IPC/Net Exploit Tests\n");
    printf("==============================================\n");

    test_secure_ipc_redteam();
    test_tnet_redteam();

    printf("\n==============================================\n");
    printf("  Result: %d passed, %d failed, %d total\n",
           tests_passed, tests_failed, tests_total);
    printf("==============================================\n");

    return (tests_failed == 0) ? 0 : 1;
}
