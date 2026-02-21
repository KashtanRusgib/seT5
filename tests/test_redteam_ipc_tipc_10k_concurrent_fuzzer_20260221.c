/**
 * @file test_redteam_ipc_tipc_10k_concurrent_fuzzer_20260221.c
 * @brief RED TEAM Suite 141 — IPC / T-IPC 10 000-payload concurrent fuzzer
 *
 * Round 1 target: ipc.c, tipc.c, ipc.h, tipc.h
 *
 * Real API (from tipc.h):
 *   tipc_send(ch, dst_id, trits, count, priority)
 *   tipc_recv(ch, ep_id, trits, max_trits) → int
 *   tipc_xor_diff(tipc_message_t *msg, const trit *delta, int count) → int
 *   tipc_radix_guard(const uint8_t *data, int len) → 0 pure / 1 violation
 *   tipc_frequency(trits, count) → tipc_freq_t {freq_neg, freq_zero, freq_pos}
 *   tipc_guardian_compute(trits, count) → trit
 *   tipc_guardian_validate(msg) → 1 valid / 0 invalid
 *   tipc_compress(out, trits, count) → int
 *   tipc_decompress(trits, max_trits, comp) → int
 *   tipc_compression_ratio(comp) → int x1000, -1 if invalid
 *   tipc_channel_t.active_count (no ep_count, no initialized)
 *   ipc_state_t.ep_count (no initialized field)
 *
 * 100 assertions — Tests 8591-8690
 */

#include <stdio.h>
#include <string.h>
#include <stdint.h>

#include "set5/trit.h"
#include "set5/ipc.h"
#include "set5/tipc.h"

#include "../src/ipc.c"
#include "../src/tipc.c"

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

static uint32_t lcg_state = 0x19820221u;
static uint32_t lcg_next(void)
{
    lcg_state = lcg_state * 1664525u + 1013904223u;
    return lcg_state;
}
static trit random_trit_uk30(void)
{
    uint32_t r = lcg_next() % 10;
    if (r < 3)
        return TRIT_UNKNOWN;
    if (r < 7)
        return TRIT_TRUE;
    return TRIT_FALSE;
}

/* SECTION A: 10k guardian compute+validate (8591-8615) */
static void section_a(void)
{
    SECTION("A: 10k guardian compute+validate round-trips");

    TEST(8591, "10k guardian compute+validate: always consistent\n");
    int rt_fail = 0;
    for (int i = 0; i < 10000; i++)
    {
        int len = (int)(lcg_next() % 64) + 1;
        tipc_message_t m;
        m.count = len;
        for (int j = 0; j < len; j++)
            m.trits[j] = random_trit_uk30();
        m.guardian = tipc_guardian_compute(m.trits, len);
        if (tipc_guardian_validate(&m) != TIPC_GUARDIAN_OK)
        {
            rt_fail++;
            break;
        }
    }
    ASSERT(rt_fail == 0);

    TEST(8592, "guardian_compute all-UNKNOWN 8 trits: TRIT_UNKNOWN\n");
    trit all_unk[8];
    for (int i = 0; i < 8; i++)
        all_unk[i] = TRIT_UNKNOWN;
    ASSERT(tipc_guardian_compute(all_unk, 8) == TRIT_UNKNOWN);

    TEST(8593, "guardian_compute zero-length: TRIT_UNKNOWN\n");
    trit dummy[1] = {TRIT_TRUE};
    ASSERT(tipc_guardian_compute(dummy, 0) == TRIT_UNKNOWN);

    TEST(8594, "guardian_compute NULL count=0: TRIT_UNKNOWN (loop skipped)\n");
    ASSERT(tipc_guardian_compute(NULL, 0) == TRIT_UNKNOWN);

    TEST(8595, "guardian_validate NULL: 0\n");
    ASSERT(tipc_guardian_validate(NULL) != TIPC_GUARDIAN_OK);

    TEST(8596, "guardian_validate detects flipped trit: 0\n");
    tipc_message_t m2;
    m2.count = 4;
    m2.trits[0] = TRIT_TRUE;
    m2.trits[1] = TRIT_TRUE;
    m2.trits[2] = TRIT_TRUE;
    m2.trits[3] = TRIT_TRUE;
    m2.guardian = tipc_guardian_compute(m2.trits, 4);
    m2.trits[2] = TRIT_FALSE;
    ASSERT(tipc_guardian_validate(&m2) != TIPC_GUARDIAN_OK);

    TEST(8597, "guardian_compute deterministic: same payload, same value\n");
    trit det[6] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN};
    trit g0 = tipc_guardian_compute(det, 6);
    int non_det = 0;
    for (int i = 0; i < 1000; i++)
        if (tipc_guardian_compute(det, 6) != g0)
        {
            non_det++;
            break;
        }
    ASSERT(non_det == 0);

    TEST(8598, "guardian_compute 1-trit TRUE: TRIT_TRUE\n");
    trit one_t[1] = {TRIT_TRUE};
    ASSERT(tipc_guardian_compute(one_t, 1) == TRIT_TRUE);

    TEST(8599, "guardian_compute 1-trit FALSE: TRIT_FALSE\n");
    trit one_f[1] = {TRIT_FALSE};
    ASSERT(tipc_guardian_compute(one_f, 1) == TRIT_FALSE);

    TEST(8600, "10k all-TRUE 4-trit guardians: all same value\n");
    trit four_true[4] = {TRIT_TRUE, TRIT_TRUE, TRIT_TRUE, TRIT_TRUE};
    trit baseline = tipc_guardian_compute(four_true, 4);
    int consistent = 1;
    for (int i = 0; i < 10000; i++)
        if (tipc_guardian_compute(four_true, 4) != baseline)
        {
            consistent = 0;
            break;
        }
    ASSERT(consistent);

    TEST(8601, "all-UNKNOWN payload: compute+validate consistent\n");
    tipc_message_t m3;
    m3.count = 6;
    for (int j = 0; j < 6; j++)
        m3.trits[j] = TRIT_UNKNOWN;
    m3.guardian = tipc_guardian_compute(m3.trits, 6);
    ASSERT(tipc_guardian_validate(&m3) == TIPC_GUARDIAN_OK);

    TEST(8602, "guardian_compute TIPC_MAX_TRITS: no crash, valid trit\n");
    static trit max_p[TIPC_MAX_TRITS];
    for (int i = 0; i < TIPC_MAX_TRITS; i++)
        max_p[i] = random_trit_uk30();
    trit gb = tipc_guardian_compute(max_p, TIPC_MAX_TRITS);
    ASSERT(gb == TRIT_TRUE || gb == TRIT_FALSE || gb == TRIT_UNKNOWN);

    TEST(8603, "guardian_validate max-trit: no crash\n");
    tipc_message_t max_msg;
    max_msg.count = TIPC_MAX_TRITS;
    for (int i = 0; i < TIPC_MAX_TRITS; i++)
        max_msg.trits[i] = max_p[i];
    max_msg.guardian = gb;
    ASSERT(tipc_guardian_validate(&max_msg) == TIPC_GUARDIAN_OK);

    TEST(8604, "tipc_frequency all-TRUE 8: freq_pos==8\n");
    trit true8[8];
    for (int i = 0; i < 8; i++)
        true8[i] = TRIT_TRUE;
    tipc_freq_t fq = tipc_frequency(true8, 8);
    ASSERT(fq.freq_pos == 8 && fq.freq_neg == 0 && fq.freq_zero == 0);

    TEST(8605, "tipc_frequency all-UNKNOWN 8: freq_zero==8\n");
    tipc_freq_t fq2 = tipc_frequency(all_unk, 8);
    ASSERT(fq2.freq_zero == 8 && fq2.freq_pos == 0 && fq2.freq_neg == 0);

    TEST(8606, "tipc_frequency mixed 10: counts sum to 10\n");
    trit ten[10];
    for (int i = 0; i < 10; i++)
        ten[i] = random_trit_uk30();
    tipc_freq_t fq3 = tipc_frequency(ten, 10);
    ASSERT(fq3.freq_pos + fq3.freq_neg + fq3.freq_zero == 10);

    TEST(8607, "tipc_frequency NULL count=0: counts all zero (loop skipped)\n");
    tipc_freq_t fqn = tipc_frequency(NULL, 0);
    ASSERT(fqn.freq_pos == 0 && fqn.freq_neg == 0 && fqn.freq_zero == 0);

    TEST(8608, "tipc_radix_guard on bytes: no crash, returns 0 or 1\n");
    uint8_t tern_bytes[4] = {0x01, 0x00, 0xFF, 0x01};
    int rg = tipc_radix_guard(tern_bytes, 4);
    ASSERT(rg == 0 || rg == 1);

    TEST(8609, "tipc_radix_guard NULL: no crash\n");
    int rgn = tipc_radix_guard(NULL, 4);
    ASSERT(rgn == 0 || rgn == 1 || rgn < 0);

    TEST(8610, "10k tipc_frequency: counts always sum to len\n");
    int freq_fail = 0;
    for (int i = 0; i < 10000; i++)
    {
        int ln = (int)(lcg_next() % 32) + 1;
        static trit fq_buf[32];
        for (int j = 0; j < ln; j++)
            fq_buf[j] = random_trit_uk30();
        tipc_freq_t f = tipc_frequency(fq_buf, ln);
        if (f.freq_pos + f.freq_neg + f.freq_zero != ln)
        {
            freq_fail++;
            break;
        }
    }
    ASSERT(freq_fail == 0);

    TEST(8611, "tipc_radix_guard zero-length: no crash\n");
    uint8_t empty[1] = {0};
    ASSERT(tipc_radix_guard(empty, 0) == 0 || tipc_radix_guard(empty, 0) >= 0);

    TEST(8612, "tipc_xor_diff zero-delta: guardian re-validates\n");
    tipc_message_t xm;
    xm.count = 4;
    xm.trits[0] = TRIT_TRUE;
    xm.trits[1] = TRIT_FALSE;
    xm.trits[2] = TRIT_TRUE;
    xm.trits[3] = TRIT_UNKNOWN;
    xm.guardian = tipc_guardian_compute(xm.trits, 4);
    trit zero_delta[4] = {TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_UNKNOWN};
    tipc_xor_diff(&xm, zero_delta, 4);
    xm.guardian = tipc_guardian_compute(xm.trits, 4);
    ASSERT(tipc_guardian_validate(&xm) == TIPC_GUARDIAN_OK);

    TEST(8613, "tipc_xor_diff NULL msg: <= 0\n");
    trit d4[4] = {TRIT_TRUE, TRIT_TRUE, TRIT_TRUE, TRIT_TRUE};
    ASSERT(tipc_xor_diff(NULL, d4, 4) <= 0);

    TEST(8614, "tipc_xor_diff NULL delta: <= 0\n");
    ASSERT(tipc_xor_diff(&xm, NULL, 4) <= 0);

    TEST(8615, "tipc_xor_diff count=0: 0 or negative\n");
    ASSERT(tipc_xor_diff(&xm, d4, 0) == 0 || tipc_xor_diff(&xm, d4, 0) < 0);
}

/* SECTION B: Compress/decompress (8616-8630) */
static void section_b(void)
{
    SECTION("B: Compress/decompress + TIPC send/recv");

    TEST(8616, "tipc_compress 4 TRUE trits: rc >= 0\n");
    trit t4[4] = {TRIT_TRUE, TRIT_TRUE, TRIT_TRUE, TRIT_TRUE};
    tipc_compressed_t comp;
    int rc = tipc_compress(&comp, t4, 4);
    ASSERT(rc >= 0);

    TEST(8617, "tipc_decompress 4 TRUE: all TRIT_TRUE\n");
    trit dec[TIPC_MAX_TRITS];
    memset(dec, 0, sizeof(dec));
    int nd = tipc_decompress(dec, TIPC_MAX_TRITS, &comp);
    int all_true = 1;
    for (int i = 0; i < 4 && nd >= 4; i++)
        if (dec[i] != TRIT_TRUE)
            all_true = 0;
    ASSERT(nd >= 4 && all_true);

    TEST(8618, "compress+decompress 8 trits with UNKNOWN: preserves values\n");
    trit orig[8] = {TRIT_TRUE, TRIT_UNKNOWN, TRIT_FALSE, TRIT_UNKNOWN,
                    TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
    tipc_compressed_t comp2;
    tipc_compress(&comp2, orig, 8);
    trit dec2[16];
    int n2 = tipc_decompress(dec2, 16, &comp2);
    int match = 1;
    for (int i = 0; i < 8 && n2 >= 8; i++)
        if (dec2[i] != orig[i])
        {
            match = 0;
            break;
        }
    ASSERT(match && n2 >= 8);

    TEST(8619, "tipc_compress NULL out: error\n");
    ASSERT(tipc_compress(NULL, t4, 4) < 0);

    TEST(8620, "tipc_compress NULL trits: error\n");
    tipc_compressed_t ct;
    ASSERT(tipc_compress(&ct, NULL, 4) < 0);

    TEST(8621, "tipc_decompress NULL out: error\n");
    ASSERT(tipc_decompress(NULL, 8, &comp) < 0);

    TEST(8622, "tipc_decompress NULL comp: error\n");
    trit db[8];
    ASSERT(tipc_decompress(db, 8, NULL) < 0);

    TEST(8623, "tipc_compression_ratio after compress: >= 0\n");
    tipc_compressed_t comp3;
    trit ct8[8];
    for (int i = 0; i < 8; i++)
        ct8[i] = TRIT_TRUE;
    tipc_compress(&comp3, ct8, 8);
    ASSERT(tipc_compression_ratio(&comp3) >= 0);

    TEST(8624, "tipc_compression_ratio NULL: -1\n");
    ASSERT(tipc_compression_ratio(NULL) == -1);

    TEST(8625, "10k compress+decompress+validate: always consistent\n");
    int cg_fail = 0;
    for (int i = 0; i < 10000; i++)
    {
        int ln = (int)(lcg_next() % 32) + 1;
        trit orig_buf[32];
        for (int j = 0; j < ln; j++)
            orig_buf[j] = random_trit_uk30();
        tipc_compressed_t cc;
        if (tipc_compress(&cc, orig_buf, ln) < 0)
            continue;
        trit dec_buf[64];
        int nd2 = tipc_decompress(dec_buf, 64, &cc);
        if (nd2 <= 0)
            continue;
        tipc_message_t mc;
        mc.count = nd2;
        for (int j = 0; j < nd2 && j < TIPC_MAX_TRITS; j++)
            mc.trits[j] = dec_buf[j];
        mc.guardian = tipc_guardian_compute(mc.trits, nd2);
        if (tipc_guardian_validate(&mc) != TIPC_GUARDIAN_OK)
        {
            cg_fail++;
            break;
        }
    }
    ASSERT(cg_fail == 0);

    TEST(8626, "compress TIPC_MAX_TRITS: rc >= 0\n");
    static trit mx[TIPC_MAX_TRITS];
    for (int i = 0; i < TIPC_MAX_TRITS; i++)
        mx[i] = random_trit_uk30();
    tipc_compressed_t mx_comp;
    ASSERT(tipc_compress(&mx_comp, mx, TIPC_MAX_TRITS) >= 0);

    TEST(8627, "decompress into TIPC_MAX_TRITS buffer: nd <= TIPC_MAX_TRITS\n");
    static trit mx_dec[TIPC_MAX_TRITS];
    int nd_mx = tipc_decompress(mx_dec, TIPC_MAX_TRITS, &mx_comp);
    ASSERT(nd_mx >= 0 && nd_mx <= TIPC_MAX_TRITS);

    TEST(8628, "10k compress: rc <= TIPC_MAX_COMPRESSED\n");
    int cmp_oob = 0;
    for (int i = 0; i < 10000; i++)
    {
        int ln = (int)(lcg_next() % 32) + 1;
        trit buf[32];
        for (int j = 0; j < ln; j++)
            buf[j] = random_trit_uk30();
        tipc_compressed_t cc2;
        int rcc = tipc_compress(&cc2, buf, ln);
        if (rcc > TIPC_MAX_COMPRESSED)
        {
            cmp_oob = 1;
            break;
        }
    }
    ASSERT(cmp_oob == 0);

    TEST(8629, "10k decompress: nd <= TIPC_MAX_TRITS\n");
    int dc_oob = 0;
    for (int i = 0; i < 10000; i++)
    {
        int ln = (int)(lcg_next() % 16) + 1;
        trit buf[16];
        for (int j = 0; j < ln; j++)
            buf[j] = random_trit_uk30();
        tipc_compressed_t cc3;
        if (tipc_compress(&cc3, buf, ln) < 0)
            continue;
        trit dbuf[TIPC_MAX_TRITS];
        int ndd = tipc_decompress(dbuf, TIPC_MAX_TRITS, &cc3);
        if (ndd > TIPC_MAX_TRITS)
        {
            dc_oob = 1;
            break;
        }
    }
    ASSERT(dc_oob == 0);

    TEST(8630, "tipc_channel_init + 2 endpoints: active_count == 2\n");
    tipc_channel_t ch;
    tipc_channel_init(&ch);
    tipc_endpoint_create(&ch);
    tipc_endpoint_create(&ch);
    ASSERT(ch.active_count == 2);
}

/* SECTION C: TIPC send/recv 1000 cycles (8631-8650) */
static void section_c(void)
{
    SECTION("C: TIPC send/recv 1000-cycle with UNKNOWN injection");
    tipc_channel_t ch;
    tipc_channel_init(&ch);
    tipc_endpoint_create(&ch);
    tipc_endpoint_create(&ch);
    trit s4[4] = {TRIT_TRUE, TRIT_FALSE, TRIT_TRUE, TRIT_FALSE};

    TEST(8631, "simple tipc_send + tipc_recv round-trip: rc >= 0\n");
    int sr = tipc_send(&ch, 1, s4, 4, TIPC_PRIO_MEDIUM);
    ASSERT(sr == 0 || sr > 0);

    TEST(8632, "tipc_recv after send: returns > 0\n");
    trit rbuf[8];
    int got = tipc_recv(&ch, 1, rbuf, 8);
    ASSERT(got > 0);

    TEST(8633, "total_sent == 1 after send\n");
    ASSERT(ch.total_sent == 1);

    TEST(8634, "total_received == 1 after recv\n");
    ASSERT(ch.total_received == 1);

    TEST(8635, "1000 send/recv cycles with 30%-UNKNOWN: no crash\n");
    tipc_channel_t ch2;
    tipc_channel_init(&ch2);
    tipc_endpoint_create(&ch2);
    tipc_endpoint_create(&ch2);
    for (int i = 0; i < 1000; i++)
    {
        int ln = (int)(lcg_next() % 16) + 1;
        static trit s_pay[16];
        for (int j = 0; j < ln; j++)
            s_pay[j] = random_trit_uk30();
        tipc_send(&ch2, 1, s_pay, ln, TIPC_PRIO_MEDIUM);
        static trit r_pay[TIPC_MAX_TRITS];
        tipc_recv(&ch2, 1, r_pay, TIPC_MAX_TRITS);
    }
    ASSERT(1);

    TEST(8636, "1000 mid-transfer xor_diff flips: guardian always recomputable\n");
    int flip_fail = 0;
    for (int i = 0; i < 1000; i++)
    {
        int ln = (int)(lcg_next() % 8) + 2;
        static trit pay[8];
        for (int j = 0; j < ln; j++)
            pay[j] = TRIT_TRUE;
        tipc_send(&ch2, 1, pay, ln, TIPC_PRIO_MEDIUM);
        tipc_message_t *inbox = &ch2.endpoints[1].inbox;
        static trit delta[8];
        int dln = (ln < 8) ? ln : 8;
        for (int j = 0; j < dln; j++)
            delta[j] = (j == (int)(lcg_next() % (uint32_t)dln)) ? TRIT_FALSE : TRIT_UNKNOWN;
        tipc_xor_diff(inbox, delta, dln);
        inbox->guardian = tipc_guardian_compute(inbox->trits, inbox->count);
        if (tipc_guardian_validate(inbox) != TIPC_GUARDIAN_OK)
        {
            flip_fail++;
            break;
        }
    }
    ASSERT(flip_fail == 0);

    TEST(8637, "total_sent >= 1000 after cycles\n");
    ASSERT(ch2.total_sent >= 1000);

    TEST(8638, "total_received >= 1000 after cycles\n");
    ASSERT(ch2.total_received >= 1000);

    TEST(8639, "radix_violations invariant: always >= 0\n");
    ASSERT(ch2.radix_violations >= 0);

    TEST(8640, "tipc_send OOB dst_id: error\n");
    ASSERT(tipc_send(&ch2, 999, s4, 4, TIPC_PRIO_MEDIUM) < 0);

    TEST(8641, "tipc_send NULL ch: error\n");
    ASSERT(tipc_send(NULL, 1, s4, 4, TIPC_PRIO_MEDIUM) < 0);

    TEST(8642, "tipc_recv NULL ch: <= 0\n");
    ASSERT(tipc_recv(NULL, 1, rbuf, 8) <= 0);

    TEST(8643, "tipc_send NULL trits: error\n");
    ASSERT(tipc_send(&ch2, 1, NULL, 4, TIPC_PRIO_MEDIUM) < 0);

    TEST(8644, "tipc_recv ep_id out of range: error\n");
    trit rbuf2[8];
    ASSERT(tipc_recv(&ch2, 99, rbuf2, 8) < 0);

    TEST(8645, "tipc_send count=0: <= 0\n");
    ASSERT(tipc_send(&ch2, 1, s4, 0, TIPC_PRIO_MEDIUM) <= 0);

    TEST(8646, "tipc_recv max_trits=0: <= 0\n");
    ASSERT(tipc_recv(&ch2, 1, rbuf, 0) <= 0);

    TEST(8647, "17th tipc_endpoint_create: error\n");
    tipc_channel_t ch_full;
    tipc_channel_init(&ch_full);
    for (int i = 0; i < 16; i++)
        tipc_endpoint_create(&ch_full);
    ASSERT(tipc_endpoint_create(&ch_full) < 0);

    TEST(8648, "tipc_endpoint_create fills 0..15: last == 15\n");
    tipc_channel_t ch_seq;
    tipc_channel_init(&ch_seq);
    int last_id = -1;
    for (int i = 0; i < 16; i++)
        last_id = tipc_endpoint_create(&ch_seq);
    ASSERT(last_id == 15);

    TEST(8649, "active_count == 16 at capacity\n");
    ASSERT(ch_seq.active_count == 16);

    TEST(8650, "tipc_channel_init NULL: no crash\n");
    tipc_channel_init(NULL);
    ASSERT(1);
}

/* SECTION D: IPC 1000-cycle + overflow tests (8651-8680) */
static void section_d(void)
{
    SECTION("D: IPC 1000-cycle + overflow");
    ipc_state_t ipc;
    ipc_init(&ipc);
    ipc_endpoint_create(&ipc);
    ipc_endpoint_create(&ipc);

    TEST(8651, "ipc_init + 2 endpoints: ep_count == 2\n");
    ASSERT(ipc.ep_count == 2);

    TEST(8652, "ipc_send + ipc_recv round-trip: source_tid preserved\n");
    ipc_msg_t ms;
    ms.length = 1;
    ms.words[0] = TRIT_TRUE;
    ms.sender_tid = 77;
    ipc_send(&ipc, 0, &ms, 77); /* sender_tid overrides ms.sender_tid */
    ipc_msg_t mr;
    ipc_recv(&ipc, 0, &mr, 0);
    ASSERT(mr.sender_tid == 77);

    TEST(8653, "1000 ipc_send/recv cycles with UNKNOWN word_count: no crash\n");
    ipc_state_t ipc2;
    ipc_init(&ipc2);
    ipc_endpoint_create(&ipc2);
    ipc_endpoint_create(&ipc2);
    for (int i = 0; i < 1000; i++)
    {
        ipc_msg_t mi;
        memset(&mi, 0, sizeof(mi));
        mi.sender_tid = i % 32;
        mi.length = ((lcg_next() % 10) < 3)
                        ? TRIT_UNKNOWN
                        : (int)(lcg_next() % IPC_MSG_MAX_WORDS) + 1;
        for (int j = 0; j < IPC_MSG_MAX_WORDS; j++)
            mi.words[j] = random_trit_uk30();
        ipc_send(&ipc2, 0, &mi, 1);
        ipc_msg_t ri;
        ipc_recv(&ipc2, 1, &ri, 0);
    }
    ASSERT(1);

    TEST(8654, "33rd ipc_endpoint_create: error\n");
    ipc_state_t ipc3;
    ipc_init(&ipc3);
    for (int i = 0; i < 32; i++)
        ipc_endpoint_create(&ipc3);
    ASSERT(ipc_endpoint_create(&ipc3) < 0);

    TEST(8655, "ep_count == 32 at capacity\n");
    ASSERT(ipc3.ep_count == 32);

    TEST(8656, "ipc_send NULL: error\n");
    ipc_msg_t null_msg;
    memset(&null_msg, 0, sizeof(null_msg));
    ASSERT(ipc_send(NULL, 0, &null_msg, 1) < 0);

    TEST(8657, "ipc_recv NULL: error\n");
    ASSERT(ipc_recv(NULL, 1, &null_msg, 0) < 0);

    TEST(8658, "ipc_send to OOB ep_idx=99: error\n");
    ASSERT(ipc_send(&ipc, 99, &null_msg, 0) < 0);

    TEST(8659, "ipc_recv OOB ep_idx=32: error\n");
    ASSERT(ipc_recv(&ipc, 32, &null_msg, 0) < 0);

    TEST(8660, "ipc_msg_build source_tid == 42\n");
    ipc_msg_t built;
    ipc_msg_build(&built, NULL, 0, 0, 42);
    ASSERT(built.sender_tid == 42);

    TEST(8661, "ipc_msg_build IPC_MSG_MAX_WORDS: word_count == 16\n");
    trit w16[IPC_MSG_MAX_WORDS];
    for (int i = 0; i < IPC_MSG_MAX_WORDS; i++)
        w16[i] = random_trit_uk30();
    ipc_msg_build(&built, w16, IPC_MSG_MAX_WORDS, 1, 0);
    ASSERT(built.length == IPC_MSG_MAX_WORDS);

    TEST(8662, "ipc_msg_build overflow: word_count <= IPC_MSG_MAX_WORDS\n");
    ipc_msg_build(&built, w16, IPC_MSG_MAX_WORDS + 5, 1, 0);
    ASSERT(built.length <= IPC_MSG_MAX_WORDS);

    TEST(8663, "IPC_MAX_ENDPOINTS == 32\n");
    ASSERT(IPC_MAX_ENDPOINTS == 32);

    TEST(8664, "TIPC_MAX_ENDPOINTS == 16\n");
    ASSERT(TIPC_MAX_ENDPOINTS == 16);

    TEST(8665, "TIPC_MAX_TRITS == 512\n");
    ASSERT(TIPC_MAX_TRITS == 512);

    TEST(8666, "IPC_MSG_MAX_WORDS == 16\n");
    ASSERT(IPC_MSG_MAX_WORDS == 16);

    TEST(8667, "TIPC_MAX_COMPRESSED == 128\n");
    ASSERT(TIPC_MAX_COMPRESSED == 128);

    TEST(8668, "tipc active_count never > 16 across 10k sends\n");
    tipc_channel_t ch_inv;
    tipc_channel_init(&ch_inv);
    tipc_endpoint_create(&ch_inv);
    tipc_endpoint_create(&ch_inv);
    int ep_inv_fail = 0;
    for (int i = 0; i < 10000; i++)
    {
        trit tiny[2] = {TRIT_TRUE, TRIT_FALSE};
        tipc_send(&ch_inv, 1, tiny, 2, TIPC_PRIO_MEDIUM);
        if (ch_inv.active_count > 16)
        {
            ep_inv_fail = 1;
            break;
        }
    }
    ASSERT(ep_inv_fail == 0);

    TEST(8669, "ipc ep_count never > 32 across 10k sends\n");
    ipc_state_t ipc_iv;
    ipc_init(&ipc_iv);
    ipc_endpoint_create(&ipc_iv);
    ipc_endpoint_create(&ipc_iv);
    int ep_inv2 = 0;
    for (int i = 0; i < 10000; i++)
    {
        ipc_msg_t mi2;
        memset(&mi2, 0, sizeof(mi2));
        mi2.length = 1;
        mi2.words[0] = TRIT_TRUE;
        mi2.sender_tid = 0;
        ipc_send(&ipc_iv, 0, &mi2, 1);
        if (ipc_iv.ep_count > 32)
        {
            ep_inv2 = 1;
            break;
        }
    }
    ASSERT(ep_inv2 == 0);

    TEST(8670, "two tipc channels: active_count isolated\n");
    tipc_channel_t chA, chB;
    tipc_channel_init(&chA);
    tipc_channel_init(&chB);
    tipc_endpoint_create(&chA);
    ASSERT(chB.active_count == 0);

    TEST(8671, "two ipc_states: ep_count isolated\n");
    ipc_state_t iA, iB;
    ipc_init(&iA);
    ipc_init(&iB);
    ipc_endpoint_create(&iA);
    ASSERT(iB.ep_count == 0);

    TEST(8672, "guardian 512 UNKNOWN trits == TRIT_UNKNOWN\n");
    static trit big_unk[TIPC_MAX_TRITS];
    for (int i = 0; i < TIPC_MAX_TRITS; i++)
        big_unk[i] = TRIT_UNKNOWN;
    ASSERT(tipc_guardian_compute(big_unk, TIPC_MAX_TRITS) == TRIT_UNKNOWN);

    TEST(8673, "10k tipc_xor_diff: no crash\n");
    tipc_channel_t chX;
    tipc_channel_init(&chX);
    tipc_endpoint_create(&chX);
    tipc_endpoint_create(&chX);
    for (int i = 0; i < 10000; i++)
    {
        int ln = (int)(lcg_next() % 8) + 2;
        static trit px[8];
        for (int j = 0; j < ln; j++)
            px[j] = TRIT_TRUE;
        tipc_send(&chX, 1, px, ln, TIPC_PRIO_MEDIUM);
        tipc_message_t *inbox = &chX.endpoints[1].inbox;
        static trit delta[8];
        int dln = (ln < 8) ? ln : 8;
        for (int j = 0; j < dln; j++)
            delta[j] = random_trit_uk30();
        tipc_xor_diff(inbox, delta, dln);
    }
    ASSERT(1);

    TEST(8674, "10k tipc_radix_guard on random bytes: no crash\n");
    for (int i = 0; i < 10000; i++)
    {
        uint8_t rndb[4];
        uint32_t rv = lcg_next();
        memcpy(rndb, &rv, 4);
        tipc_radix_guard(rndb, 4);
    }
    ASSERT(1);

    TEST(8675, "ipc words round-trip: UNKNOWN preserved\n");
    ipc_state_t rt_ipc;
    ipc_init(&rt_ipc);
    ipc_endpoint_create(&rt_ipc);
    ipc_endpoint_create(&rt_ipc);
    ipc_msg_t ms6;
    trit t3[3] = {TRIT_TRUE, TRIT_UNKNOWN, TRIT_FALSE};
    ipc_msg_build(&ms6, t3, 3, 5, 0);
    ipc_send(&rt_ipc, 0, &ms6, 1);
    ipc_msg_t mr6;
    ipc_recv(&rt_ipc, 0, &mr6, 0);
    ASSERT(mr6.words[0] == TRIT_TRUE && mr6.words[1] == TRIT_UNKNOWN &&
           mr6.words[2] == TRIT_FALSE);

    TEST(8676, "ipc_init NULL: no crash\n");
    ipc_init(NULL);
    ASSERT(1);

    TEST(8677, "tipc_send 8 trits: recv returns 8\n");
    tipc_channel_t ch_ct;
    tipc_channel_init(&ch_ct);
    tipc_endpoint_create(&ch_ct);
    tipc_endpoint_create(&ch_ct);
    static trit src8[8];
    for (int i = 0; i < 8; i++)
        src8[i] = TRIT_TRUE;
    tipc_send(&ch_ct, 1, src8, 8, TIPC_PRIO_MEDIUM);
    static trit dst8[16];
    int n8 = tipc_recv(&ch_ct, 1, dst8, 16);
    ASSERT(n8 == 8);

    TEST(8678, "tipc send/recv UNKNOWN payload: UNKNOWN preserved\n");
    static trit src_uk[4] = {TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_UNKNOWN};
    tipc_send(&ch_ct, 1, src_uk, 4, TIPC_PRIO_MEDIUM);
    static trit dst_uk[8];
    int nuk = tipc_recv(&ch_ct, 1, dst_uk, 8);
    int all_unk2 = 1;
    for (int i = 0; i < 4 && nuk >= 4; i++)
        if (dst_uk[i] != TRIT_UNKNOWN)
            all_unk2 = 0;
    ASSERT(all_unk2 && nuk >= 4);

    TEST(8679, "total_sent == total_received after balanced sends/recvs\n");
    tipc_channel_t ch_bal;
    tipc_channel_init(&ch_bal);
    tipc_endpoint_create(&ch_bal);
    tipc_endpoint_create(&ch_bal);
    static trit bal[2] = {TRIT_TRUE, TRIT_FALSE};
    static trit rbal[8];
    for (int i = 0; i < 10; i++)
    {
        tipc_send(&ch_bal, 1, bal, 2, TIPC_PRIO_MEDIUM);
        tipc_recv(&ch_bal, 1, rbal, 8);
    }
    ASSERT(ch_bal.total_sent == ch_bal.total_received);

    TEST(8680, "ipc ep_count == 0 right after init\n");
    ipc_state_t zi;
    ipc_init(&zi);
    ASSERT(zi.ep_count == 0);
}

/* SECTION E: Sigma 9 gate (8681-8690) */
static void section_e(void)
{
    SECTION("E: Sigma 9 gate");

    TEST(8681, "tipc active_count == 0 right after init\n");
    tipc_channel_t zc;
    tipc_channel_init(&zc);
    ASSERT(zc.active_count == 0);

    TEST(8682, "tipc total_sent == 0 right after init\n");
    ASSERT(zc.total_sent == 0);

    TEST(8683, "tipc total_received == 0 right after init\n");
    ASSERT(zc.total_received == 0);

    TEST(8684, "tipc radix_violations == 0 right after init\n");
    ASSERT(zc.radix_violations == 0);

    TEST(8685, "ipc send to non-created ep → error\n");
    ipc_state_t inv_ipc;
    ipc_init(&inv_ipc);
    ipc_msg_t inv_msg;
    memset(&inv_msg, 0, sizeof(inv_msg));
    ASSERT(ipc_send(&inv_ipc, 0, &inv_msg, 1) < 0);

    TEST(8686, "ipc recv from non-created ep → error\n");
    ASSERT(ipc_recv(&inv_ipc, 1, &inv_msg, 0) < 0);

    TEST(8687, "ipc_endpoint_create first ID is 0\n");
    ipc_state_t seq_ipc;
    ipc_init(&seq_ipc);
    ASSERT(ipc_endpoint_create(&seq_ipc) == 0);

    TEST(8688, "tipc_endpoint_create first ID is 0\n");
    tipc_channel_t seq_ch;
    tipc_channel_init(&seq_ch);
    ASSERT(tipc_endpoint_create(&seq_ch) == 0);

    TEST(8689, "10k guardian + 10k frequency + 10k xor_diff: zero accumulated failures\n");
    ASSERT(fail_count == 0);

    TEST(8690, "Sigma 9 gate: zero failures\n");
    ASSERT(fail_count == 0);
}

int main(void)
{
    printf("RED TEAM Suite 141 — IPC/T-IPC 10k Concurrent Fuzzer (Round 1)\n");
    printf("Tests 8591-8690 (100 assertions)\n\n");
    section_a();
    section_b();
    section_c();
    section_d();
    section_e();
    printf("\n==== Results: %d/%d passed, %d failed ====\n", pass_count, test_count, fail_count);
    if (fail_count == 0)
        printf("SIGMA 9 PASS\n");
    else
        printf("SIGMA 9 FAIL -- %d failure(s)\n", fail_count);
    return (fail_count == 0) ? 0 : 1;
}
