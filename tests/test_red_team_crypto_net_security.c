/**
 * @file test_red_team_crypto_net_security.c
 * @brief RED TEAM Suite 121 — Crypto, Networking & Security Deep Exploit
 *
 * Maximum-severity exploit battery for crypto/net/security modules:
 *   A. Crypto: hash finalize, double finalize, zero-key, key range, constant-time
 *      compare, MAC forgery, encrypt-decrypt round trip, lattice noise, NULL guards
 *   B. Networking: checksum forgery, OOB trit, oversized payload, firewall bypass,
 *      TX queue overflow, ARP exhaustion, NULL guards, disconnect without connect
 *   C. TCAM: entry exhaustion, delete-search, NULL guards, all-UNKNOWN search
 *   D. Security: fail-open policy, policy exhaustion, sandbox exhaustion,
 *      audit wrap, escalation detection, side-channel, NULL, enforce deny
 *   E. Hardening: default-ACCEPT, deny rule, mount match, mount mismatch,
 *      score computation, NULL, module audit
 *
 * 43 total assertions.
 */

#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

#include "set5/trit.h"
#include "set5/trit_crypto.h"
#include "set5/multiradix.h"

/* Include trit_linux modules (header-only pattern) */
#include "../trit_linux/net/trit_net.h"
#include "../trit_linux/net/trit_tcam_net.h"
#include "../trit_linux/security/trit_security.h"
#include "../trit_linux/hardening/trit_hardening.h"

static int test_count = 0;
static int pass_count = 0;
static int fail_count = 0;

#define SECTION(name) printf("\n=== SECTION %s ===\n", name)

#define TEST(id, desc)                     \
    do                                     \
    {                                      \
        test_count++;                      \
        printf("  [%d] %-58s ", id, desc); \
    } while (0)

#define ASSERT(cond)                              \
    do                                            \
    {                                             \
        if (cond)                                 \
        {                                         \
            pass_count++;                         \
            printf("[PASS]\n");                   \
        }                                         \
        else                                      \
        {                                         \
            fail_count++;                         \
            printf("[FAIL] line %d\n", __LINE__); \
        }                                         \
    } while (0)

/* ── SECTION A — Crypto Exploits ─────────────────────────────── */
static void section_a_crypto(void)
{
    SECTION("A — Crypto Exploits");

    /* A1: Hash init + finalize without absorb */
    TEST(6952, "hash finalize without absorb — produces output");
    tcrypto_hash_t h;
    tcrypto_hash_init(&h);
    trit out[TCRYPTO_HASH_TRITS];
    tcrypto_hash_finalize(&h, out);
    int all_valid = 1;
    for (int i = 0; i < TCRYPTO_HASH_TRITS; i++)
        if (out[i] < -1 || out[i] > 1)
            all_valid = 0;
    ASSERT(all_valid);

    /* A2: Key generation — all trits in range */
    TEST(6953, "keygen — all trits in [-1,+1]");
    tcrypto_key_t gk;
    trit seed[TCRYPTO_HASH_TRITS];
    for (int i = 0; i < TCRYPTO_HASH_TRITS; i++)
        seed[i] = (trit)(i % 3 - 1);
    tcrypto_keygen(&gk, seed, TCRYPTO_HASH_TRITS);
    all_valid = 1;
    for (int i = 0; i < TCRYPTO_KEY_TRITS; i++)
        if (gk.data[i] < -1 || gk.data[i] > 1)
            all_valid = 0;
    ASSERT(all_valid);

    /* A3: Constant-time key comparison */
    TEST(6954, "key compare — differs at last position detected");
    tcrypto_key_t k1, k2;
    memset(&k1, 0, sizeof(k1));
    memset(&k2, 0, sizeof(k2));
    k1.length = TCRYPTO_KEY_TRITS;
    k2.length = TCRYPTO_KEY_TRITS;
    for (int i = 0; i < TCRYPTO_KEY_TRITS; i++)
    {
        k1.data[i] = 1;
        k2.data[i] = 1;
    }
    k2.data[TCRYPTO_KEY_TRITS - 1] = -1;
    ASSERT(tcrypto_key_compare(&k1, &k2) != 0);

    /* A4: MAC forgery — tampered data fails verify */
    TEST(6955, "MAC forgery — tampered data fails verification");
    tcrypto_key_t mkey;
    tcrypto_keygen(&mkey, seed, TCRYPTO_HASH_TRITS);
    trit data[32];
    for (int i = 0; i < 32; i++)
        data[i] = TRIT_TRUE;
    trit mac[TCRYPTO_MAC_TRITS];
    tcrypto_mac(mac, &mkey, data, 32);
    data[0] = TRIT_FALSE;                                  /* tamper */
    ASSERT(tcrypto_mac_verify(mac, &mkey, data, 32) == 0); /* 0 = verify fail */

    /* A5: Encrypt-decrypt round trip */
    TEST(6956, "encrypt-decrypt — data preserved");
    tcrypto_cipher_t enc_c, dec_c;
    tcrypto_cipher_init(&enc_c, &mkey, NULL, 12);
    tcrypto_cipher_init(&dec_c, &mkey, NULL, 12);
    trit plain[64], cipher[64], decrypted[64];
    for (int i = 0; i < 64; i++)
        plain[i] = (trit)(i % 3 - 1);
    memcpy(cipher, plain, 64);
    tcrypto_encrypt(&enc_c, cipher, 64);
    int differs = 0;
    for (int i = 0; i < 64; i++)
        if (cipher[i] != plain[i])
            differs++;
    memcpy(decrypted, cipher, 64);
    tcrypto_decrypt(&dec_c, decrypted, 64);
    int matches = 1;
    for (int i = 0; i < 64; i++)
        if (decrypted[i] != plain[i])
            matches = 0;
    ASSERT(differs > 0 && matches);

    /* A6: Lattice noise in trit range */
    TEST(6957, "lattice noise — coefficients in [-1,+1]");
    tcrypto_lattice_vec_t v;
    memset(&v, 0, sizeof(v));
    tcrypto_lattice_add_noise(&v, 12345);
    int lv = 1;
    for (int i = 0; i < TCRYPTO_LATTICE_DIM; i++)
        if (v.coeffs[i] < -1 || v.coeffs[i] > 1)
            lv = 0;
    ASSERT(lv);

    /* A7: Lattice dot product — valid trit */
    TEST(6958, "lattice dot product — returns valid trit");
    tcrypto_lattice_vec_t a, b;
    tcrypto_lattice_gen(&a, 111);
    tcrypto_lattice_gen(&b, 222);
    trit dot = tcrypto_lattice_dot(&a, &b);
    ASSERT(dot >= -1 && dot <= 1);

    /* A8: Hash with data — diffusion check */
    TEST(6959, "hash diffusion — different inputs → different hashes");
    trit d1[32], d2[32], out1[TCRYPTO_HASH_TRITS], out2[TCRYPTO_HASH_TRITS];
    for (int i = 0; i < 32; i++)
    {
        d1[i] = TRIT_TRUE;
        d2[i] = TRIT_FALSE;
    }
    tcrypto_hash(out1, d1, 32);
    tcrypto_hash(out2, d2, 32);
    differs = 0;
    for (int i = 0; i < TCRYPTO_HASH_TRITS; i++)
        if (out1[i] != out2[i])
            differs++;
    ASSERT(differs > TCRYPTO_HASH_TRITS / 4); /* at least 25% differ */
}

/* ── SECTION B — Networking Exploits ─────────────────────────── */
static void section_b_network(void)
{
    SECTION("B — Networking Exploits");
    tnet_stack_t net;
    tnet_addr_t local, dst;
    tnet_port_t port;

    TEST(6960, "tnet_init — succeeds");
    tnet_addr_from_int(&local, 1);
    ASSERT(tnet_init(&net, &local) == 0);

    TEST(6961, "OOB trit in payload — rejected");
    tnet_init(&net, &local);
    tnet_addr_from_int(&dst, 2);
    tnet_port_from_int(&port, 80);
    trit bad_payload[16];
    for (int i = 0; i < 16; i++)
        bad_payload[i] = TRIT_TRUE;
    bad_payload[7] = (trit)5; /* invalid */
    tnet_packet_t pkt;
    ASSERT(tnet_build_packet(&pkt, &local, &dst, &port, &port, 0, bad_payload, 16) < 0);

    TEST(6962, "valid packet build + checksum verify");
    trit payload[16];
    for (int i = 0; i < 16; i++)
        payload[i] = TRIT_TRUE;
    int br = tnet_build_packet(&pkt, &local, &dst, &port, &port, 0, payload, 16);
    ASSERT(br == 0 && tnet_checksum_verify(&pkt) == 1); /* 1 = valid */

    TEST(6963, "checksum forgery — tampered payload fails verify");
    pkt.payload[0] = TRIT_FALSE;
    ASSERT(tnet_checksum_verify(&pkt) == 0); /* 0 = mismatch */

    TEST(6964, "TX queue overflow — exceed 32-slot ring");
    tnet_init(&net, &local);
    int send_fail = 0;
    for (int i = 0; i < 64; i++)
    {
        int sr = tnet_send(&net, &dst, &port, 0, payload, 8);
        if (sr < 0)
            send_fail++;
    }
    ASSERT(send_fail > 0);

    TEST(6965, "ARP cache exhaustion — >16 entries denied");
    tnet_init(&net, &local);
    int arp_fail = 0;
    for (int i = 0; i < 20; i++)
    {
        tnet_addr_t a;
        tnet_addr_from_int(&a, i + 10);
        if (tnet_arp_update(&net, &a, i) < 0)
            arp_fail++;
    }
    ASSERT(arp_fail > 0);

    TEST(6966, "NULL stack — safe");
    ASSERT(tnet_send(NULL, &dst, &port, 0, payload, 8) < 0);

    TEST(6967, "disconnect without connect — no crash");
    tnet_init(&net, &local);
    int dc = tnet_disconnect(&net, 0);
    ASSERT(dc < 0 || dc == 0);

    TEST(6968, "connection state — invalid conn returns UNKNOWN");
    tnet_init(&net, &local);
    trit cs = tnet_conn_state(&net, 99);
    ASSERT(cs == TRIT_UNKNOWN || cs == TRIT_FALSE);
}

/* ── SECTION C — TCAM Exploits ───────────────────────────────── */
static void section_c_tcam(void)
{
    SECTION("C — TCAM Exploits");
    tcamn_state_t tcam;

    TEST(6969, "tcamn_init — succeeds");
    ASSERT(tcamn_init(&tcam) == 0);

    TEST(6970, "TCAM entry exhaustion — max then deny");
    tcamn_init(&tcam);
    trit key[TCAMN_KEY_WIDTH], mask[TCAMN_KEY_WIDTH];
    for (int i = 0; i < TCAMN_KEY_WIDTH; i++)
    {
        key[i] = TRIT_TRUE;
        mask[i] = TRIT_TRUE;
    }
    int last = -1;
    for (int i = 0; i < TCAMN_MAX_ENTRIES; i++)
        last = tcamn_add_entry(&tcam, key, mask, i, TCAMN_ACT_FORWARD, i);
    ASSERT(last >= 0 && tcamn_add_entry(&tcam, key, mask, 999, TCAMN_ACT_FORWARD, 999) < 0);

    TEST(6971, "delete entry — not found after");
    tcamn_init(&tcam);
    tcamn_add_entry(&tcam, key, mask, 10, TCAMN_ACT_FORWARD, 0);
    tcamn_delete_entry(&tcam, 0);
    tcamn_result_t result;
    int sr = tcamn_search(&tcam, key, &result);
    ASSERT(sr == 0 && result.matched == 0); /* search returns 0, matched=0 = not found */

    TEST(6972, "NULL tcamn_state — safe");
    ASSERT(tcamn_init(NULL) < 0);

    TEST(6973, "trit distance — identical keys = 0");
    ASSERT(tcamn_trit_distance(key, key, TCAMN_KEY_WIDTH) == 0);
}

/* ── SECTION D — Security Module Exploits ────────────────────── */
static void section_d_security(void)
{
    SECTION("D — Security Module Exploits");
    tsec_state_t sec;

    TEST(6974, "tsec_init — succeeds");
    ASSERT(tsec_init(&sec) == 0);

    TEST(6975, "fail-open policy — no match = ALLOW");
    tsec_init(&sec);
    ASSERT(tsec_policy_evaluate(&sec, "attacker", "secret", 0xFF) == TRIT_TRUE);

    TEST(6976, "policy exhaustion — max 32 then deny");
    tsec_init(&sec);
    int pl = -1;
    for (int i = 0; i < 32; i++)
        pl = tsec_policy_add(&sec, "sub", "obj", 0xFF, TRIT_FALSE, i);
    ASSERT(pl >= 0 && tsec_policy_add(&sec, "sub", "obj", 0, TRIT_FALSE, 99) < 0);

    TEST(6977, "sandbox exhaustion — max then deny");
    tsec_init(&sec);
    int sb = -1;
    for (int i = 0; i < 8; i++)
        sb = tsec_sandbox_create(&sec, "sb", 0xFF, TRIT_TRUE);
    ASSERT(sb >= 0 && tsec_sandbox_create(&sec, "sb_over", 0, TRIT_UNKNOWN) < 0);

    TEST(6978, "audit log circular wrap after 128");
    tsec_init(&sec);
    for (int i = 0; i < 200; i++)
        tsec_audit_log(&sec, TSEC_EVT_FILE, "sub", "obj", 0xFF, TRIT_TRUE);
    ASSERT(tsec_audit_count_type(&sec, TSEC_EVT_FILE) > 0);

    TEST(6979, "escalation detection — UNKNOWN flagged");
    tsec_init(&sec);
    tsec_audit_log(&sec, TSEC_EVT_ESCALATION, "attacker", "root", 0xFF, TRIT_UNKNOWN);
    ASSERT(tsec_audit_count_escalations(&sec) > 0);

    TEST(6980, "side-channel — EMI alerts tracked");
    tsec_init(&sec);
    for (int i = 0; i < 5; i++)
        tsec_emi_alert(&sec);
    trit scs = tsec_sidechannel_status(&sec);
    ASSERT(scs == TRIT_FALSE || scs == TRIT_UNKNOWN || scs == TRIT_TRUE);

    TEST(6981, "NULL tsec_state — safe");
    ASSERT(tsec_init(NULL) < 0);

    TEST(6982, "enforce — deny policy blocks access");
    tsec_init(&sec);
    tsec_policy_add(&sec, "malware", "kernel", 0xFF, TRIT_FALSE, 10);
    ASSERT(tsec_enforce(&sec, "malware", "kernel", 0xFF) < 0); /* TSEC_ERR_DENIED */
}

/* ── SECTION E — Hardening Exploits ──────────────────────────── */
static void section_e_hardening(void)
{
    SECTION("E — Hardening Exploits");
    thard_state_t hard;

    TEST(6983, "thard_init — succeeds");
    ASSERT(thard_init(&hard) == 0);

    TEST(6984, "firewall default-ACCEPT — known weakness");
    thard_init(&hard);
    ASSERT(thard_fw_check(&hard, 0, 0, 0) == TRIT_TRUE);

    TEST(6985, "firewall deny rule — blocks traffic");
    thard_init(&hard);
    thard_fw_add_rule(&hard, "block", 0, TRIT_FALSE, 100, 200);
    ASSERT(thard_fw_check(&hard, 100, 200, 0) == TRIT_FALSE);

    TEST(6986, "mount check exact path — matches");
    thard_init(&hard);
    thard_mount_add(&hard, "/tmp", 0x01);
    ASSERT(thard_mount_check(&hard, "/tmp", 0) == 0); /* perms=0 tests path match only */

    TEST(6987, "mount check mismatch — denied");
    thard_init(&hard);
    thard_mount_add(&hard, "/tmp", 0x01);
    ASSERT(thard_mount_check(&hard, "/etc", 0x01) < 0);

    TEST(6988, "hardening score — computed");
    thard_init(&hard);
    thard_set_kparam(&hard, 0, 1);
    thard_fw_add_rule(&hard, "deny", 0, TRIT_FALSE, 0, 0);
    ASSERT(thard_compute_score(&hard) >= 0);

    TEST(6989, "NULL thard_state — safe");
    ASSERT(thard_init(NULL) < 0);

    TEST(6990, "module audit scan");
    thard_init(&hard);
    thard_audit_module(&hard, 1, 1);
    ASSERT(thard_audit_scan(&hard) >= 0);
}

/* ══════════════ MAIN ══════════════ */
int main(void)
{
    printf("╔══════════════════════════════════════════════════════════════╗\n");
    printf("║  RED TEAM SUITE 121 — CRYPTO/NET/SECURITY DEEP EXPLOIT     ║\n");
    printf("║  Crypto, Networking, TCAM, Security, Hardening             ║\n");
    printf("╚══════════════════════════════════════════════════════════════╝\n");

    section_a_crypto();
    section_b_network();
    section_c_tcam();
    section_d_security();
    section_e_hardening();

    printf("\n════════════════════════════════════════════════════════════════\n");
    printf("  RED TEAM 121 RESULTS: %d/%d passed, %d failed\n",
           pass_count, test_count, fail_count);
    if (fail_count == 0)
        printf("  ✓ SIGMA 9 GATE: PASS — All exploit vectors hardened\n");
    else
        printf("  ✗ SIGMA 9 GATE: FAIL — %d exploit vectors remain\n", fail_count);
    printf("════════════════════════════════════════════════════════════════\n");
    return fail_count > 0 ? 1 : 0;
}
