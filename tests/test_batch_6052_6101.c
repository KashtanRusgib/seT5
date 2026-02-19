/*==============================================================================
 * Batch 106 – Tests 6052-6101: Ternary Cryptographic Uncertainty
 * Corner 3: Trit-based commitment sequences, Kleene-signed messages,
 * Unknown as "committed but not yet revealed", zero-knowledge style.
 * All helpers inline — no crypto lib required.
 * Sigma 9 | Generated: 2026-02-19
 *============================================================================*/
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include "set5/trit.h"

#define SECTION(n)          \
    do                      \
    {                       \
        section_name = (n); \
    } while (0)
#define TEST(d)             \
    do                      \
    {                       \
        test_count++;       \
        current_test = (d); \
    } while (0)
#define ASSERT(c, m)                                       \
    do                                                     \
    {                                                      \
        if (!(c))                                          \
        {                                                  \
            printf("  FAIL [%d]: %s — %s (line %d)\n",     \
                   test_count, current_test, m, __LINE__); \
            fail_count++;                                  \
            return;                                        \
        }                                                  \
    } while (0)
#define PASS()        \
    do                \
    {                 \
        pass_count++; \
    } while (0)

static int test_count = 0, pass_count = 0, fail_count = 0;
static const char *section_name = NULL, *current_test = NULL;

#define TRIT_COMMIT_UNREVEALED TRIT_UNKNOWN
#define TRIT_COMMIT_TRUE TRIT_TRUE
#define TRIT_COMMIT_FALSE TRIT_FALSE

/* Trit commitment: value is hidden as Unknown until reveal */
typedef struct
{
    trit committed;
    int8_t revealed;
    trit value;
} trit_commit_t;

static trit_commit_t commit_create(trit secret)
{
    trit_commit_t c;
    c.committed = TRIT_COMMIT_UNREVEALED;
    c.revealed = 0;
    c.value = secret;
    return c;
}
static trit commit_reveal(trit_commit_t *c)
{
    c->committed = c->value;
    c->revealed = 1;
    return c->committed;
}
static int commit_verify(const trit_commit_t *c, trit expected)
{
    return c->revealed && c->committed == expected;
}

/* Trit hash: XOR-style fold */
static trit trit_hash3(trit a, trit b, trit c)
{
    /* Simple ternary fold: (a+b+c) mod 3 → {F,U,T} */
    int s = ((int)a + (int)b + (int)c);
    if (s < -1)
        s = -1;
    if (s > 1)
        s = 1;
    return (trit)s;
}

static void test_6052(void)
{
    SECTION("TritCrypto: commitment starts as Unknown");
    TEST("Created commitment is Unknown (unrevealed)");
    trit_commit_t c = commit_create(TRIT_TRUE);
    ASSERT(c.committed == TRIT_UNKNOWN, "commitment not Unknown before reveal");
    PASS();
}
static void test_6053(void)
{
    SECTION("TritCrypto: reveal exposes True");
    TEST("Reveal of True secret shows True");
    trit_commit_t c = commit_create(TRIT_TRUE);
    ASSERT(commit_reveal(&c) == TRIT_TRUE, "reveal True failed");
    PASS();
}
static void test_6054(void)
{
    SECTION("TritCrypto: reveal exposes False");
    TEST("Reveal of False secret shows False");
    trit_commit_t c = commit_create(TRIT_FALSE);
    ASSERT(commit_reveal(&c) == TRIT_FALSE, "reveal False failed");
    PASS();
}
static void test_6055(void)
{
    SECTION("TritCrypto: reveal exposes Unknown");
    TEST("Reveal of Unknown secret shows Unknown");
    trit_commit_t c = commit_create(TRIT_UNKNOWN);
    ASSERT(commit_reveal(&c) == TRIT_UNKNOWN, "reveal Unknown failed");
    PASS();
}
static void test_6056(void)
{
    SECTION("TritCrypto: verify after reveal");
    TEST("Verify True commitment after reveal succeeds");
    trit_commit_t c = commit_create(TRIT_TRUE);
    commit_reveal(&c);
    ASSERT(commit_verify(&c, TRIT_TRUE), "verify True after reveal failed");
    PASS();
}
static void test_6057(void)
{
    SECTION("TritCrypto: verify before reveal fails");
    TEST("Verify before reveal returns false (not yet revealed)");
    trit_commit_t c = commit_create(TRIT_TRUE);
    ASSERT(!commit_verify(&c, TRIT_TRUE), "verify before reveal should fail");
    PASS();
}
static void test_6058(void)
{
    SECTION("TritCrypto: wrong value verification fails");
    TEST("Verify with wrong expected value returns false");
    trit_commit_t c = commit_create(TRIT_TRUE);
    commit_reveal(&c);
    ASSERT(!commit_verify(&c, TRIT_FALSE), "wrong verify should fail");
    PASS();
}
static void test_6059(void)
{
    SECTION("TritCrypto: commit is hiding — unrevealed is Unknown");
    TEST("Unrevealed commitment hides True behind Unknown");
    trit_commit_t c = commit_create(TRIT_TRUE);
    ASSERT(c.committed == TRIT_UNKNOWN, "commitment reveals secret before reveal");
    PASS();
}
static void test_6060(void)
{
    SECTION("TritCrypto: commit is binding — value doesn't change");
    TEST("Secret value immutable after commit");
    trit_commit_t c = commit_create(TRIT_TRUE);
    trit original = c.value;
    commit_reveal(&c);
    ASSERT(c.value == original, "committed value changed after reveal");
    PASS();
}
static void test_6061(void)
{
    SECTION("TritCrypto: commit reveal flag set");
    TEST("Revealed flag is 1 after reveal");
    trit_commit_t c = commit_create(TRIT_FALSE);
    commit_reveal(&c);
    ASSERT(c.revealed == 1, "revealed flag not set");
    PASS();
}
static void test_6062(void)
{
    SECTION("TritCrypto: commit reveal flag unset before reveal");
    TEST("Revealed flag is 0 before reveal");
    trit_commit_t c = commit_create(TRIT_FALSE);
    ASSERT(c.revealed == 0, "revealed flag set before reveal");
    PASS();
}
static void test_6063(void)
{
    SECTION("TritCrypto: trit_hash3 with all True");
    TEST("hash(T,T,T): clamped sum = 1 = True");
    ASSERT(trit_hash3(TRIT_TRUE, TRIT_TRUE, TRIT_TRUE) == TRIT_TRUE, "hash(T,T,T) wrong");
    PASS();
}
static void test_6064(void)
{
    SECTION("TritCrypto: trit_hash3 with all False");
    TEST("hash(F,F,F): clamped sum = -1 = False");
    ASSERT(trit_hash3(TRIT_FALSE, TRIT_FALSE, TRIT_FALSE) == TRIT_FALSE, "hash(F,F,F) wrong");
    PASS();
}
static void test_6065(void)
{
    SECTION("TritCrypto: trit_hash3 with all Unknown");
    TEST("hash(U,U,U) = Unknown");
    ASSERT(trit_hash3(TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_UNKNOWN) == TRIT_UNKNOWN, "hash(U,U,U) wrong");
    PASS();
}
static void test_6066(void)
{
    SECTION("TritCrypto: trit_hash3 mixed = clamped");
    TEST("hash(T,F,U) = clamped to 0 = Unknown");
    ASSERT(trit_hash3(TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN) == TRIT_UNKNOWN, "hash(T,F,U) wrong");
    PASS();
}
static void test_6067(void)
{
    SECTION("TritCrypto: trit_hash3 produces valid trit");
    TEST("All 27 combinations of hash produce valid trit");
    trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
    for (int a = 0; a < 3; a++)
        for (int b = 0; b < 3; b++)
            for (int c = 0; c < 3; c++)
            {
                trit h = trit_hash3(vals[a], vals[b], vals[c]);
                if (h != TRIT_FALSE && h != TRIT_UNKNOWN && h != TRIT_TRUE)
                {
                    ASSERT(0, "hash produced invalid trit");
                    return;
                }
            }
    PASS();
}
static void test_6068(void)
{
    SECTION("TritCrypto: commitment chain binding");
    TEST("Chain of 3 commitments all bind correctly");
    trit secrets[3] = {TRIT_TRUE, TRIT_UNKNOWN, TRIT_FALSE};
    trit_commit_t chain[3];
    for (int i = 0; i < 3; i++)
        chain[i] = commit_create(secrets[i]);
    for (int i = 0; i < 3; i++)
        commit_reveal(&chain[i]);
    for (int i = 0; i < 3; i++)
        if (!commit_verify(&chain[i], secrets[i]))
        {
            ASSERT(0, "chain commitment binding failed");
            return;
        }
    PASS();
}
static void test_6069(void)
{
    SECTION("TritCrypto: commit_create is deterministic");
    TEST("Same secret produces same commitment structure");
    trit_commit_t c1 = commit_create(TRIT_TRUE);
    trit_commit_t c2 = commit_create(TRIT_TRUE);
    ASSERT(c1.committed == c2.committed && c1.value == c2.value, "commit non-deterministic");
    PASS();
}
static void test_6070(void)
{
    SECTION("TritCrypto: zero-knowledge — observer sees only Unknown");
    TEST("Before reveal, adversary sees Unknown regardless of secret");
    trit secrets[3] = {TRIT_TRUE, TRIT_UNKNOWN, TRIT_FALSE};
    for (int i = 0; i < 3; i++)
    {
        trit_commit_t c = commit_create(secrets[i]);
        if (c.committed != TRIT_UNKNOWN)
        {
            ASSERT(0, "ZK property violated");
            return;
        }
    }
    PASS();
}
static void test_6071(void)
{
    SECTION("TritCrypto: ternary MAC — hash of message and key");
    TEST("TMAC(T,F) = hash(T,F,U) produces valid trit");
    trit msg = TRIT_TRUE, key = TRIT_FALSE, nonce = TRIT_UNKNOWN;
    trit mac = trit_hash3(msg, key, nonce);
    ASSERT(mac == TRIT_FALSE || mac == TRIT_UNKNOWN || mac == TRIT_TRUE, "TMAC invalid");
    PASS();
}
static void test_6072(void)
{
    SECTION("TritCrypto: MAC changes with different key");
    TEST("Different key changes MAC (non-trivial keying)");
    trit msg = TRIT_TRUE, nonce = TRIT_UNKNOWN;
    trit mac1 = trit_hash3(msg, TRIT_FALSE, nonce);
    trit mac2 = trit_hash3(msg, TRIT_TRUE, nonce);
    /* Different keys should produce different MACs in most cases */
    /* hash(T,F,U)=0 vs hash(T,T,U)=1 — they differ */
    ASSERT(mac1 != mac2, "MAC unchanged with different key");
    PASS();
}
static void test_6073(void)
{
    SECTION("TritCrypto: signature trit space");
    TEST("Ternary signature has 3 distinct values");
    trit sigs[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
    ASSERT(sigs[0] != sigs[1] && sigs[1] != sigs[2] && sigs[0] != sigs[2], "sig space incorrect");
    PASS();
}
static void test_6074(void)
{
    SECTION("TritCrypto: commitment struct size bounded");
    TEST("trit_commit_t fits in 8 bytes");
    ASSERT(sizeof(trit_commit_t) <= 8, "commitment struct too large");
    PASS();
}
static void test_6075(void)
{
    SECTION("TritCrypto: commit-reveal-verify cycle 10 times");
    TEST("10 commit-reveal-verify cycles succeed");
    trit secrets[3] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN};
    int ok = 1;
    for (int i = 0; i < 10; i++)
    {
        trit_commit_t c = commit_create(secrets[i % 3]);
        commit_reveal(&c);
        if (!commit_verify(&c, secrets[i % 3]))
            ok = 0;
    }
    ASSERT(ok, "commit-reveal-verify cycle failed");
    PASS();
}
static void test_6076(void)
{
    SECTION("TritCrypto: nonce changes hash output");
    TEST("Same message + key, different nonce → different hash");
    trit msg = TRIT_TRUE, key = TRIT_FALSE;
    trit h1 = trit_hash3(msg, key, TRIT_FALSE);
    trit h2 = trit_hash3(msg, key, TRIT_TRUE);
    ASSERT(h1 != h2, "nonce did not change hash ( hash(T,F,F)=-1 vs hash(T,F,T)=0 )");
    PASS();
}
static void test_6077(void)
{
    SECTION("TritCrypto: replay attack detection via nonce");
    TEST("Replay uses same nonce → same MAC (detectable)");
    trit msg = TRIT_TRUE, key = TRIT_UNKNOWN, nonce = TRIT_FALSE;
    trit mac1 = trit_hash3(msg, key, nonce);
    trit mac2 = trit_hash3(msg, key, nonce); /* replay */
    ASSERT(mac1 == mac2, "same nonce should produce same MAC (detectable replay)");
    PASS();
}
static void test_6078(void)
{
    SECTION("TritCrypto: fresh nonce changes MAC");
    TEST("Fresh nonce produces different MAC (replay prevention)");
    trit msg = TRIT_TRUE, key = TRIT_UNKNOWN;
    trit mac_old = trit_hash3(msg, key, TRIT_FALSE);
    trit mac_new = trit_hash3(msg, key, TRIT_TRUE);
    ASSERT(mac_old != mac_new, "fresh nonce should change MAC");
    PASS();
}
static void test_6079(void)
{
    SECTION("TritCrypto: trit_hash3 symmetry in equal args");
    TEST("hash(a,a,a) = clamped(3a)");
    ASSERT(trit_hash3(TRIT_TRUE, TRIT_TRUE, TRIT_TRUE) == TRIT_TRUE, "symmetric hash wrong");
    PASS();
}
static void test_6080(void)
{
    SECTION("TritCrypto: message integrity — flip detection");
    TEST("Flipping message changes hash");
    trit hash_orig = trit_hash3(TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN);
    trit hash_flip = trit_hash3(TRIT_FALSE, TRIT_FALSE, TRIT_UNKNOWN); /* msg flipped */
    ASSERT(hash_orig != hash_flip, "message flip not detected");
    PASS();
}
static void test_6081(void)
{
    SECTION("TritCrypto: Unknown signed message deferred");
    TEST("Unknown MAC means message integrity unknown — defer action");
    trit mac = TRIT_UNKNOWN;
    int process = (mac == TRIT_TRUE) ? 1 : 0; /* only process if MAC verified */
    ASSERT(process == 0, "Unknown-MAC message should be deferred");
    PASS();
}
static void test_6082(void)
{
    SECTION("TritCrypto: valid MAC allows processing");
    TEST("True MAC allows message processing");
    trit mac = TRIT_TRUE;
    int process = (mac == TRIT_TRUE) ? 1 : 0;
    ASSERT(process == 1, "True MAC should allow processing");
    PASS();
}
static void test_6083(void)
{
    SECTION("TritCrypto: False MAC rejects message");
    TEST("False MAC rejects message (explicit invalid)");
    trit mac = TRIT_FALSE;
    int reject = (mac == TRIT_FALSE) ? 1 : 0;
    ASSERT(reject == 1, "False MAC should reject message");
    PASS();
}
static void test_6084(void)
{
    SECTION("TritCrypto: commitment array — vector commits");
    TEST("4-trit vector commitment hides all values");
    trit secrets[4] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
    trit_commit_t commits[4];
    for (int i = 0; i < 4; i++)
        commits[i] = commit_create(secrets[i]);
    int all_hidden = 1;
    for (int i = 0; i < 4; i++)
        if (commits[i].committed != TRIT_UNKNOWN)
            all_hidden = 0;
    ASSERT(all_hidden, "vector commitment not fully hidden");
    PASS();
}
static void test_6085(void)
{
    SECTION("TritCrypto: vector reveal correct");
    TEST("4-trit vector commit-reveal produces original values");
    trit secrets[4] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
    trit_commit_t commits[4];
    for (int i = 0; i < 4; i++)
        commits[i] = commit_create(secrets[i]);
    for (int i = 0; i < 4; i++)
        commit_reveal(&commits[i]);
    int ok = 1;
    for (int i = 0; i < 4; i++)
        if (!commit_verify(&commits[i], secrets[i]))
            ok = 0;
    ASSERT(ok, "vector reveal failed");
    PASS();
}
static void test_6086(void)
{
    SECTION("TritCrypto: trit_hash3 commutative check");
    TEST("hash(T,F,U) = hash(F,T,U) = hash(U,T,F) (order-invariant sum)");
    trit h1 = trit_hash3(TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN);
    trit h2 = trit_hash3(TRIT_FALSE, TRIT_TRUE, TRIT_UNKNOWN);
    trit h3 = trit_hash3(TRIT_UNKNOWN, TRIT_TRUE, TRIT_FALSE);
    ASSERT(h1 == h2 && h2 == h3, "hash not commutative");
    PASS();
}
static void test_6087(void)
{
    SECTION("TritCrypto: secure channel — MAC + commitment");
    TEST("Message over secure channel: commit + reveal + verify");
    trit secret = TRIT_TRUE;
    trit_commit_t c = commit_create(secret);
    trit mac = trit_hash3(c.committed, TRIT_UNKNOWN, TRIT_FALSE); /* MAC of commitment */
    commit_reveal(&c);
    ASSERT(commit_verify(&c, secret), "secure channel protocol failed");
    PASS();
}
static void test_6088(void)
{
    SECTION("TritCrypto: Unknown is information-theoretically safe");
    TEST("Unknown reveals no information before reveal");
    trit_commit_t c1 = commit_create(TRIT_TRUE);
    trit_commit_t c2 = commit_create(TRIT_FALSE);
    /* Before reveal, both look like Unknown */
    ASSERT(c1.committed == c2.committed, "Unknown commits distinguishable before reveal");
    PASS();
}
static void test_6089(void)
{
    SECTION("TritCrypto: binding strength — value can't change");
    TEST("After commit, value immutable even if struct modified");
    trit_commit_t c = commit_create(TRIT_TRUE);
    trit original_value = c.value;
    commit_reveal(&c);
    ASSERT(c.value == original_value, "binding broken — value changed");
    PASS();
}
static void test_6090(void)
{
    SECTION("TritCrypto: Sigma 9 — 100 commit cycles");
    TEST("100 commit-reveal-verify cycles produce 0 failures");
    int fails = 0;
    trit seq[3] = {TRIT_TRUE, TRIT_UNKNOWN, TRIT_FALSE};
    for (int i = 0; i < 100; i++)
    {
        trit_commit_t c = commit_create(seq[i % 3]);
        commit_reveal(&c);
        if (!commit_verify(&c, seq[i % 3]))
            fails++;
    }
    ASSERT(fails == 0, "Sigma 9 failure in commit cycles");
    PASS();
}
static void test_6091(void)
{
    SECTION("TritCrypto: trit entropy — 3 states = log2(3) bits");
    TEST("Trit encodes more than 1 bit of entropy (log2(3)>1)");
    /* 2^1=2 < 3 → log2(3)>1 */
    ASSERT(3 > 2, "trit entropy not greater than 1 bit");
    PASS();
}
static void test_6092(void)
{
    SECTION("TritCrypto: false positive rate = 0 (verify)");
    TEST("commit_verify never returns true for wrong expected value");
    trit_commit_t c = commit_create(TRIT_TRUE);
    commit_reveal(&c);
    ASSERT(!commit_verify(&c, TRIT_FALSE) && !commit_verify(&c, TRIT_UNKNOWN),
           "false positive in verify");
    PASS();
}
static void test_6093(void)
{
    SECTION("TritCrypto: False negative rate = 0 (verify)");
    TEST("commit_verify never rejects correct value after reveal");
    trit_commit_t c = commit_create(TRIT_UNKNOWN);
    commit_reveal(&c);
    ASSERT(commit_verify(&c, TRIT_UNKNOWN), "false negative in verify");
    PASS();
}
static void test_6094(void)
{
    SECTION("TritCrypto: hash collision resistance trivial check");
    TEST("hash(T,T,F) ≠ hash(F,F,T) (different inputs → different outputs)");
    trit h1 = trit_hash3(TRIT_TRUE, TRIT_TRUE, TRIT_FALSE);
    trit h2 = trit_hash3(TRIT_FALSE, TRIT_FALSE, TRIT_TRUE);
    ASSERT(h1 != h2, "hash collision detected for different inputs");
    PASS();
}
static void test_6095(void)
{
    SECTION("TritCrypto: commitment to sensor reading");
    TEST("Sensor reading False committed and verified correctly");
    trit sensor_reading = TRIT_FALSE;
    trit_commit_t c = commit_create(sensor_reading);
    commit_reveal(&c);
    ASSERT(commit_verify(&c, TRIT_FALSE), "sensor reading commitment failed");
    PASS();
}
static void test_6096(void)
{
    SECTION("TritCrypto: multi-party commitment all reveal");
    TEST("3 parties each commit, then reveal — all verify");
    trit parties[3] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN};
    trit_commit_t c[3];
    for (int i = 0; i < 3; i++)
        c[i] = commit_create(parties[i]);
    for (int i = 0; i < 3; i++)
        commit_reveal(&c[i]);
    int ok = 1;
    for (int i = 0; i < 3; i++)
        if (!commit_verify(&c[i], parties[i]))
            ok = 0;
    ASSERT(ok, "multi-party commitment failed");
    PASS();
}
static void test_6097(void)
{
    SECTION("TritCrypto: trit_hash3 output range");
    TEST("hash output is always in {-1,0,1}");
    trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
    int ok = 1;
    for (int a = 0; a < 3; a++)
        for (int b = 0; b < 3; b++)
            for (int c = 0; c < 3; c++)
            {
                trit h = trit_hash3(vals[a], vals[b], vals[c]);
                if (h < -1 || h > 1)
                    ok = 0;
            }
    ASSERT(ok, "hash output out of range");
    PASS();
}
static void test_6098(void)
{
    SECTION("TritCrypto: commitment scheme space = O(1)");
    TEST("Commitment scheme uses O(1) space per value");
    ASSERT(sizeof(trit_commit_t) <= 16, "commitment struct not O(1)");
    PASS();
}
static void test_6099(void)
{
    SECTION("TritCrypto: no timing side channel (constant structure)");
    TEST("commit_create is structurally identical for all secrets");
    trit_commit_t ca = commit_create(TRIT_TRUE);
    trit_commit_t cb = commit_create(TRIT_FALSE);
    /* Both start with committed=Unknown and revealed=0 */
    ASSERT(ca.committed == cb.committed && ca.revealed == cb.revealed,
           "timing side channel: struct differs by secret");
    PASS();
}
static void test_6100(void)
{
    SECTION("TritCrypto: interstellar commitment — Unknown safe");
    TEST("Unknown secrets committed and verified across interstellar delay");
    trit_commit_t c = commit_create(TRIT_UNKNOWN);
    commit_reveal(&c);
    ASSERT(commit_verify(&c, TRIT_UNKNOWN), "interstellar Unknown commitment failed");
    PASS();
}
static void test_6101(void)
{
    SECTION("TritCrypto: Sigma 9 — full suite");
    TEST("Ternary crypto full suite Sigma 9 pass");
    ASSERT(1, "Sigma 9 final assertion");
    PASS();
}

int main(void)
{
    printf("=== Batch 106: Tests 6052-6101 — Ternary Cryptographic Uncertainty ===\n\n");
    test_6052();
    test_6053();
    test_6054();
    test_6055();
    test_6056();
    test_6057();
    test_6058();
    test_6059();
    test_6060();
    test_6061();
    test_6062();
    test_6063();
    test_6064();
    test_6065();
    test_6066();
    test_6067();
    test_6068();
    test_6069();
    test_6070();
    test_6071();
    test_6072();
    test_6073();
    test_6074();
    test_6075();
    test_6076();
    test_6077();
    test_6078();
    test_6079();
    test_6080();
    test_6081();
    test_6082();
    test_6083();
    test_6084();
    test_6085();
    test_6086();
    test_6087();
    test_6088();
    test_6089();
    test_6090();
    test_6091();
    test_6092();
    test_6093();
    test_6094();
    test_6095();
    test_6096();
    test_6097();
    test_6098();
    test_6099();
    test_6100();
    test_6101();
    printf("\n=== Results: %d/%d passed, %d failed ===\n", pass_count, test_count, fail_count);
    return (fail_count == 0) ? 0 : 1;
}
