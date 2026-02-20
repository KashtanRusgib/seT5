/*==============================================================================
 * Batch 109 – Tests 6202-6251: RSI Flywheel Safety & Bounded Iteration
 * Corner 3: Recursive Self-Improvement with trit guards.
 * Tests guard logic, session bounds, mutation approval/rejection, eudaimonia.
 * Sigma 9 | Generated: 2026-02-20
 *============================================================================*/
#include <stdio.h>
#include <string.h>
#include <math.h>
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

/*--- Inline RSI types and functions (standalone compilation) ----------------*/

#define RSI_MAX_LOOPS 10
#define RSI_BEAUTY_THRESHOLD 0.9
#define RSI_CURIOSITY_MIN 0.5
#define RSI_COMPACTION_INTERVAL 5

typedef struct
{
    int iteration;
    trit access_guard;
    double beauty_score;
    double curiosity_level;
    double eudaimonia;
    int mutations_applied;
    int mutations_rejected;
    int human_queries;
} rsi_session_t;

static trit rsi_trit_guard(const rsi_session_t *session, double proposed_beauty)
{
    if (!session)
        return TRIT_FALSE;
    if (session->iteration >= RSI_MAX_LOOPS)
        return TRIT_FALSE;
    if (proposed_beauty < 0.0)
        return TRIT_FALSE;
    if (proposed_beauty < RSI_BEAUTY_THRESHOLD)
        return TRIT_UNKNOWN;
    if (proposed_beauty >= RSI_BEAUTY_THRESHOLD &&
        session->curiosity_level >= RSI_CURIOSITY_MIN)
        return TRIT_TRUE;
    return TRIT_UNKNOWN;
}

static int rsi_session_init(rsi_session_t *session)
{
    if (!session)
        return -1;
    memset(session, 0, sizeof(*session));
    session->access_guard = TRIT_TRUE;
    session->beauty_score = 1.0;
    session->curiosity_level = 1.0;
    session->eudaimonia = 1.0;
    return 0;
}

static trit rsi_propose_mutation(rsi_session_t *session,
                                 double proposed_beauty,
                                 double proposed_curiosity)
{
    if (!session)
        return TRIT_FALSE;
    trit guard = rsi_trit_guard(session, proposed_beauty);
    if (guard == TRIT_FALSE)
    {
        session->mutations_rejected++;
        return TRIT_FALSE;
    }
    if (guard == TRIT_UNKNOWN)
    {
        session->human_queries++;
        return TRIT_UNKNOWN;
    }
    session->iteration++;
    session->mutations_applied++;
    session->beauty_score = proposed_beauty;
    session->curiosity_level = proposed_curiosity;
    session->eudaimonia = proposed_beauty * proposed_curiosity;
    if (session->iteration % RSI_COMPACTION_INTERVAL == 0)
    {
        session->human_queries = 0;
    }
    return TRIT_TRUE;
}

static int rsi_can_continue(const rsi_session_t *session)
{
    if (!session)
        return 0;
    return (session->iteration < RSI_MAX_LOOPS &&
            session->access_guard != TRIT_FALSE);
}

/*--- Test functions ---------------------------------------------------------*/

/* 6202: Guard returns FALSE for NULL session */
static void test_6202(void)
{
    TEST("Guard returns TRIT_FALSE for NULL session");
    trit result = rsi_trit_guard(NULL, 0.95);
    ASSERT(result == TRIT_FALSE, "NULL session must yield FALSE");
    PASS();
}

/* 6203: Guard returns UNKNOWN for beauty=0.0 (below threshold) */
static void test_6203(void)
{
    TEST("Guard returns UNKNOWN for beauty=0.0");
    rsi_session_t s;
    rsi_session_init(&s);
    trit result = rsi_trit_guard(&s, 0.0);
    ASSERT(result == TRIT_UNKNOWN, "beauty=0.0 < threshold => UNKNOWN");
    PASS();
}

/* 6204: Guard returns UNKNOWN for beauty=0.8999 (just below threshold) */
static void test_6204(void)
{
    TEST("Guard returns UNKNOWN for beauty=0.8999");
    rsi_session_t s;
    rsi_session_init(&s);
    trit result = rsi_trit_guard(&s, 0.8999);
    ASSERT(result == TRIT_UNKNOWN, "beauty=0.8999 < 0.9 => UNKNOWN");
    PASS();
}

/* 6205: Guard returns TRUE for beauty=0.9 with sufficient curiosity */
static void test_6205(void)
{
    TEST("Guard returns TRUE for beauty=0.9, curiosity=1.0");
    rsi_session_t s;
    rsi_session_init(&s);
    trit result = rsi_trit_guard(&s, 0.9);
    ASSERT(result == TRIT_TRUE, "beauty=0.9 >= threshold, curiosity=1.0 >= 0.5 => TRUE");
    PASS();
}

/* 6206: Guard returns TRUE for beauty=1.0 */
static void test_6206(void)
{
    TEST("Guard returns TRUE for beauty=1.0");
    rsi_session_t s;
    rsi_session_init(&s);
    trit result = rsi_trit_guard(&s, 1.0);
    ASSERT(result == TRIT_TRUE, "beauty=1.0 => TRUE");
    PASS();
}

/* 6207: Guard returns FALSE for negative beauty */
static void test_6207(void)
{
    TEST("Guard returns FALSE for negative beauty");
    rsi_session_t s;
    rsi_session_init(&s);
    trit result = rsi_trit_guard(&s, -0.1);
    ASSERT(result == TRIT_FALSE, "negative beauty => FALSE");
    PASS();
}

/* 6208: Guard returns FALSE when iteration >= RSI_MAX_LOOPS */
static void test_6208(void)
{
    TEST("Guard returns FALSE when iteration == RSI_MAX_LOOPS");
    rsi_session_t s;
    rsi_session_init(&s);
    s.iteration = RSI_MAX_LOOPS;
    trit result = rsi_trit_guard(&s, 0.95);
    ASSERT(result == TRIT_FALSE, "iteration at max => FALSE");
    PASS();
}

/* 6209: Guard returns FALSE when iteration exceeds RSI_MAX_LOOPS */
static void test_6209(void)
{
    TEST("Guard returns FALSE when iteration > RSI_MAX_LOOPS");
    rsi_session_t s;
    rsi_session_init(&s);
    s.iteration = RSI_MAX_LOOPS + 5;
    trit result = rsi_trit_guard(&s, 0.95);
    ASSERT(result == TRIT_FALSE, "iteration past max => FALSE");
    PASS();
}

/* 6210: Session init returns 0 on success */
static void test_6210(void)
{
    TEST("Session init returns 0 on valid pointer");
    rsi_session_t s;
    int rc = rsi_session_init(&s);
    ASSERT(rc == 0, "init must return 0");
    PASS();
}

/* 6211: Session init returns -1 on NULL */
static void test_6211(void)
{
    TEST("Session init returns -1 on NULL");
    int rc = rsi_session_init(NULL);
    ASSERT(rc == -1, "init(NULL) must return -1");
    PASS();
}

/* 6212: Session init sets iteration to 0 */
static void test_6212(void)
{
    TEST("Session init sets iteration=0");
    rsi_session_t s;
    rsi_session_init(&s);
    ASSERT(s.iteration == 0, "iteration must be 0 after init");
    PASS();
}

/* 6213: Session init sets access_guard to TRIT_TRUE */
static void test_6213(void)
{
    TEST("Session init sets access_guard=TRIT_TRUE");
    rsi_session_t s;
    rsi_session_init(&s);
    ASSERT(s.access_guard == TRIT_TRUE, "access_guard must be TRUE after init");
    PASS();
}

/* 6214: Session init sets beauty_score to 1.0 */
static void test_6214(void)
{
    TEST("Session init sets beauty_score=1.0");
    rsi_session_t s;
    rsi_session_init(&s);
    ASSERT(fabs(s.beauty_score - 1.0) < 1e-9, "beauty_score must be 1.0");
    PASS();
}

/* 6215: Session init sets curiosity_level to 1.0 */
static void test_6215(void)
{
    TEST("Session init sets curiosity_level=1.0");
    rsi_session_t s;
    rsi_session_init(&s);
    ASSERT(fabs(s.curiosity_level - 1.0) < 1e-9, "curiosity_level must be 1.0");
    PASS();
}

/* 6216: Session init sets eudaimonia to 1.0 */
static void test_6216(void)
{
    TEST("Session init sets eudaimonia=1.0");
    rsi_session_t s;
    rsi_session_init(&s);
    ASSERT(fabs(s.eudaimonia - 1.0) < 1e-9, "eudaimonia must be 1.0");
    PASS();
}

/* 6217: Session init zeros mutations_applied */
static void test_6217(void)
{
    TEST("Session init sets mutations_applied=0");
    rsi_session_t s;
    rsi_session_init(&s);
    ASSERT(s.mutations_applied == 0, "mutations_applied must be 0");
    PASS();
}

/* 6218: Session init zeros mutations_rejected */
static void test_6218(void)
{
    TEST("Session init sets mutations_rejected=0");
    rsi_session_t s;
    rsi_session_init(&s);
    ASSERT(s.mutations_rejected == 0, "mutations_rejected must be 0");
    PASS();
}

/* 6219: Session init zeros human_queries */
static void test_6219(void)
{
    TEST("Session init sets human_queries=0");
    rsi_session_t s;
    rsi_session_init(&s);
    ASSERT(s.human_queries == 0, "human_queries must be 0");
    PASS();
}

/* 6220: Propose mutation with NULL session returns FALSE */
static void test_6220(void)
{
    TEST("Propose mutation returns FALSE on NULL session");
    trit r = rsi_propose_mutation(NULL, 0.95, 0.8);
    ASSERT(r == TRIT_FALSE, "NULL session => FALSE");
    PASS();
}

/* 6221: Propose mutation approved — beauty=0.95, curiosity=0.8 */
static void test_6221(void)
{
    TEST("Propose mutation approved: beauty=0.95, curiosity=0.8");
    rsi_session_t s;
    rsi_session_init(&s);
    trit r = rsi_propose_mutation(&s, 0.95, 0.8);
    ASSERT(r == TRIT_TRUE, "good mutation => TRUE");
    ASSERT(s.mutations_applied == 1, "mutations_applied must be 1");
    ASSERT(s.iteration == 1, "iteration must advance to 1");
    PASS();
}

/* 6222: Eudaimonia computed correctly after mutation */
static void test_6222(void)
{
    TEST("Eudaimonia = beauty * curiosity after approved mutation");
    rsi_session_t s;
    rsi_session_init(&s);
    rsi_propose_mutation(&s, 0.95, 0.8);
    double expected = 0.95 * 0.8;
    ASSERT(fabs(s.eudaimonia - expected) < 1e-9, "eudaimonia must equal 0.95*0.8");
    PASS();
}

/* 6223: Propose mutation denied when beauty below threshold */
static void test_6223(void)
{
    TEST("Propose mutation returns UNKNOWN for beauty=0.5");
    rsi_session_t s;
    rsi_session_init(&s);
    trit r = rsi_propose_mutation(&s, 0.5, 0.8);
    ASSERT(r == TRIT_UNKNOWN, "beauty < threshold => UNKNOWN");
    ASSERT(s.human_queries == 1, "human_queries incremented");
    PASS();
}

/* 6224: Propose mutation denied when beauty is negative */
static void test_6224(void)
{
    TEST("Propose mutation returns FALSE for beauty=-1.0");
    rsi_session_t s;
    rsi_session_init(&s);
    trit r = rsi_propose_mutation(&s, -1.0, 0.8);
    ASSERT(r == TRIT_FALSE, "negative beauty => FALSE");
    ASSERT(s.mutations_rejected == 1, "mutations_rejected incremented");
    PASS();
}

/* 6225: can_continue returns 0 for NULL */
static void test_6225(void)
{
    TEST("rsi_can_continue returns 0 for NULL");
    ASSERT(rsi_can_continue(NULL) == 0, "NULL => cannot continue");
    PASS();
}

/* 6226: can_continue returns 1 on fresh session */
static void test_6226(void)
{
    TEST("rsi_can_continue returns 1 on fresh session");
    rsi_session_t s;
    rsi_session_init(&s);
    ASSERT(rsi_can_continue(&s) == 1, "fresh session can continue");
    PASS();
}

/* 6227: can_continue returns 0 when access_guard is FALSE */
static void test_6227(void)
{
    TEST("rsi_can_continue returns 0 when access_guard=FALSE");
    rsi_session_t s;
    rsi_session_init(&s);
    s.access_guard = TRIT_FALSE;
    ASSERT(rsi_can_continue(&s) == 0, "guard=FALSE => cannot continue");
    PASS();
}

/* 6228: can_continue returns 0 at max iterations */
static void test_6228(void)
{
    TEST("rsi_can_continue returns 0 at iteration==RSI_MAX_LOOPS");
    rsi_session_t s;
    rsi_session_init(&s);
    s.iteration = RSI_MAX_LOOPS;
    ASSERT(rsi_can_continue(&s) == 0, "at max loops => cannot continue");
    PASS();
}

/* 6229: can_continue returns 1 at iteration 9 (one before max) */
static void test_6229(void)
{
    TEST("rsi_can_continue returns 1 at iteration=9");
    rsi_session_t s;
    rsi_session_init(&s);
    s.iteration = RSI_MAX_LOOPS - 1;
    ASSERT(rsi_can_continue(&s) == 1, "iteration 9 => can still continue");
    PASS();
}

/* 6230: Bounded iteration — 10 mutations then guard denies */
static void test_6230(void)
{
    TEST("Bounded iteration: 10 approved then denied");
    rsi_session_t s;
    rsi_session_init(&s);
    int i;
    for (i = 0; i < RSI_MAX_LOOPS; i++)
    {
        trit r = rsi_propose_mutation(&s, 0.95, 0.7);
        ASSERT(r == TRIT_TRUE, "mutations 0-9 must succeed");
    }
    ASSERT(s.iteration == RSI_MAX_LOOPS, "iteration must be 10");
    trit r11 = rsi_propose_mutation(&s, 0.95, 0.7);
    ASSERT(r11 == TRIT_FALSE, "11th mutation must be rejected");
    ASSERT(s.mutations_rejected == 1, "one rejection after cap");
    PASS();
}

/* 6231: Compaction at iteration 5 resets human_queries */
static void test_6231(void)
{
    TEST("Compaction at iteration 5 resets human_queries");
    rsi_session_t s;
    rsi_session_init(&s);
    /* Accumulate some human_queries via uncertain proposals */
    rsi_propose_mutation(&s, 0.5, 0.7); /* UNKNOWN => human_queries=1 */
    rsi_propose_mutation(&s, 0.5, 0.7); /* UNKNOWN => human_queries=2 */
    ASSERT(s.human_queries == 2, "should have 2 human queries");
    /* Now do 5 successful mutations to hit compaction */
    for (int i = 0; i < 5; i++)
        rsi_propose_mutation(&s, 0.95, 0.7);
    ASSERT(s.iteration == 5, "iteration should be 5");
    ASSERT(s.human_queries == 0, "human_queries reset at compaction");
    PASS();
}

/* 6232: Compaction does NOT reset at iteration 3 */
static void test_6232(void)
{
    TEST("No compaction at iteration 3");
    rsi_session_t s;
    rsi_session_init(&s);
    rsi_propose_mutation(&s, 0.5, 0.7); /* UNKNOWN => hq=1 */
    for (int i = 0; i < 3; i++)
        rsi_propose_mutation(&s, 0.95, 0.7);
    ASSERT(s.iteration == 3, "iteration 3");
    ASSERT(s.human_queries == 1, "human_queries NOT reset at 3");
    PASS();
}

/* 6233: Guard UNKNOWN when beauty >= threshold but curiosity < min */
static void test_6233(void)
{
    TEST("Guard UNKNOWN when beauty=0.95 but curiosity=0.3");
    rsi_session_t s;
    rsi_session_init(&s);
    s.curiosity_level = 0.3; /* below RSI_CURIOSITY_MIN */
    trit r = rsi_trit_guard(&s, 0.95);
    ASSERT(r == TRIT_UNKNOWN, "high beauty but low curiosity => UNKNOWN");
    PASS();
}

/* 6234: Guard TRUE when curiosity exactly at threshold */
static void test_6234(void)
{
    TEST("Guard TRUE when curiosity=0.5 exactly (boundary)");
    rsi_session_t s;
    rsi_session_init(&s);
    s.curiosity_level = RSI_CURIOSITY_MIN;
    trit r = rsi_trit_guard(&s, 0.95);
    ASSERT(r == TRIT_TRUE, "curiosity=0.5 >= 0.5 => TRUE");
    PASS();
}

/* 6235: Guard UNKNOWN when curiosity just below threshold */
static void test_6235(void)
{
    TEST("Guard UNKNOWN when curiosity=0.4999");
    rsi_session_t s;
    rsi_session_init(&s);
    s.curiosity_level = 0.4999;
    trit r = rsi_trit_guard(&s, 0.95);
    ASSERT(r == TRIT_UNKNOWN, "curiosity=0.4999 < 0.5 => UNKNOWN");
    PASS();
}

/* 6236: RSI symmetry — guard(T) approved vs guard(F) denied */
static void test_6236(void)
{
    TEST("RSI symmetry: approved vs denied are opposites");
    rsi_session_t s;
    rsi_session_init(&s);
    trit approved = rsi_trit_guard(&s, 0.95); /* TRUE */
    trit denied = rsi_trit_guard(&s, -0.5);   /* FALSE */
    ASSERT(approved == TRIT_TRUE, "good beauty => TRUE");
    ASSERT(denied == TRIT_FALSE, "negative beauty => FALSE");
    ASSERT(approved != denied, "approved and denied must differ");
    ASSERT(approved == -denied, "T and F are negations");
    PASS();
}

/* 6237: Multiple sequential mutations track counts correctly */
static void test_6237(void)
{
    TEST("Multiple mutations track applied/rejected counts");
    rsi_session_t s;
    rsi_session_init(&s);
    rsi_propose_mutation(&s, 0.95, 0.7); /* approved */
    rsi_propose_mutation(&s, 0.92, 0.6); /* approved */
    rsi_propose_mutation(&s, -0.1, 0.8); /* rejected */
    rsi_propose_mutation(&s, 0.91, 0.8); /* approved */
    rsi_propose_mutation(&s, -0.5, 0.9); /* rejected */
    ASSERT(s.mutations_applied == 3, "3 approved");
    ASSERT(s.mutations_rejected == 2, "2 rejected");
    ASSERT(s.iteration == 3, "iteration=3 (only approved count)");
    PASS();
}

/* 6238: Beauty score updated after successful mutation */
static void test_6238(void)
{
    TEST("Beauty score updated after approved mutation");
    rsi_session_t s;
    rsi_session_init(&s);
    rsi_propose_mutation(&s, 0.93, 0.7);
    ASSERT(fabs(s.beauty_score - 0.93) < 1e-9, "beauty_score=0.93");
    PASS();
}

/* 6239: Curiosity level updated after successful mutation */
static void test_6239(void)
{
    TEST("Curiosity level updated after approved mutation");
    rsi_session_t s;
    rsi_session_init(&s);
    rsi_propose_mutation(&s, 0.95, 0.65);
    ASSERT(fabs(s.curiosity_level - 0.65) < 1e-9, "curiosity=0.65");
    PASS();
}

/* 6240: Rejected mutation does not change beauty or curiosity */
static void test_6240(void)
{
    TEST("Rejected mutation preserves beauty/curiosity");
    rsi_session_t s;
    rsi_session_init(&s);
    double orig_beauty = s.beauty_score;
    double orig_curiosity = s.curiosity_level;
    rsi_propose_mutation(&s, -0.1, 0.5);
    ASSERT(fabs(s.beauty_score - orig_beauty) < 1e-9, "beauty unchanged");
    ASSERT(fabs(s.curiosity_level - orig_curiosity) < 1e-9, "curiosity unchanged");
    PASS();
}

/* 6241: UNKNOWN mutation does not change beauty or curiosity */
static void test_6241(void)
{
    TEST("UNKNOWN mutation does not change beauty/curiosity");
    rsi_session_t s;
    rsi_session_init(&s);
    double orig_beauty = s.beauty_score;
    rsi_propose_mutation(&s, 0.5, 0.5); /* below threshold => UNKNOWN */
    ASSERT(fabs(s.beauty_score - orig_beauty) < 1e-9, "beauty unchanged on UNKNOWN");
    ASSERT(s.iteration == 0, "iteration unchanged on UNKNOWN");
    PASS();
}

/* 6242: Eudaimonia precision — 0.9 * 0.5 */
static void test_6242(void)
{
    TEST("Eudaimonia precision: 0.9 * 0.5 = 0.45");
    rsi_session_t s;
    rsi_session_init(&s);
    rsi_propose_mutation(&s, 0.9, 0.5);
    ASSERT(fabs(s.eudaimonia - 0.45) < 1e-9, "eudaimonia must be 0.45");
    PASS();
}

/* 6243: Eudaimonia with beauty=1.0, curiosity=1.0 */
static void test_6243(void)
{
    TEST("Eudaimonia = 1.0 * 1.0 = 1.0");
    rsi_session_t s;
    rsi_session_init(&s);
    rsi_propose_mutation(&s, 1.0, 1.0);
    ASSERT(fabs(s.eudaimonia - 1.0) < 1e-9, "eudaimonia must be 1.0");
    PASS();
}

/* 6244: Eudaimonia=0 when curiosity=0 */
static void test_6244(void)
{
    TEST("Eudaimonia = 0.95 * 0.0 = 0.0 when curiosity=0");
    rsi_session_t s;
    rsi_session_init(&s);
    /* curiosity=0.0 < RSI_CURIOSITY_MIN => guard returns UNKNOWN, not TRUE */
    /* We need curiosity >= 0.5 for approval. Use 0.5 then second with 0.0 fails */
    rsi_propose_mutation(&s, 0.95, 0.5); /* approved, eudaimonia=0.95*0.5 */
    /* Now curiosity_level=0.5. Next mutation with curiosity=0: guard checks current curiosity */
    /* current curiosity=0.5 >= 0.5 => TRUE => approved */
    rsi_propose_mutation(&s, 0.95, 0.0);
    ASSERT(fabs(s.eudaimonia - 0.0) < 1e-9, "eudaimonia 0.95*0.0=0.0");
    PASS();
}

/* 6245: Full loop exhaustion — 10 mutations then cannot continue */
static void test_6245(void)
{
    TEST("Full loop exhaustion: 10 mutations then can_continue=0");
    rsi_session_t s;
    rsi_session_init(&s);
    for (int i = 0; i < RSI_MAX_LOOPS; i++)
        rsi_propose_mutation(&s, 0.95, 0.7);
    ASSERT(rsi_can_continue(&s) == 0, "cannot continue after exhaustion");
    PASS();
}

/* 6246: Guard at iteration exactly 9 still allows */
static void test_6246(void)
{
    TEST("Guard at iteration=9 (one below max) allows");
    rsi_session_t s;
    rsi_session_init(&s);
    s.iteration = 9;
    trit r = rsi_trit_guard(&s, 0.95);
    ASSERT(r == TRIT_TRUE, "iteration 9 still OK");
    PASS();
}

/* 6247: Re-init session resets all fields */
static void test_6247(void)
{
    TEST("Re-init session resets all fields");
    rsi_session_t s;
    rsi_session_init(&s);
    for (int i = 0; i < 5; i++)
        rsi_propose_mutation(&s, 0.95, 0.7);
    ASSERT(s.iteration == 5, "sanity: 5 iterations before re-init");
    rsi_session_init(&s); /* re-init */
    ASSERT(s.iteration == 0, "iteration=0 after re-init");
    ASSERT(s.mutations_applied == 0, "mutations_applied=0 after re-init");
    ASSERT(s.mutations_rejected == 0, "mutations_rejected=0 after re-init");
    ASSERT(fabs(s.eudaimonia - 1.0) < 1e-9, "eudaimonia=1.0 after re-init");
    PASS();
}

/* 6248: Compaction at iteration 10 resets human_queries */
static void test_6248(void)
{
    TEST("Compaction at iteration 10 (multiple of 5) resets hq");
    rsi_session_t s;
    rsi_session_init(&s);
    /* Accumulate queries */
    rsi_propose_mutation(&s, 0.5, 0.7); /* UNKNOWN hq=1 */
    rsi_propose_mutation(&s, 0.5, 0.7); /* UNKNOWN hq=2 */
    rsi_propose_mutation(&s, 0.5, 0.7); /* UNKNOWN hq=3 */
    /* Now do 10 successful mutations */
    for (int i = 0; i < RSI_MAX_LOOPS; i++)
        rsi_propose_mutation(&s, 0.95, 0.7);
    /* iteration=10, 10%5==0 => hq reset */
    ASSERT(s.human_queries == 0, "hq reset at iteration 10");
    PASS();
}

/* 6249: Guard UNKNOWN for beauty=0.0 is distinct from FALSE */
static void test_6249(void)
{
    TEST("Guard UNKNOWN for beauty=0.0 is not FALSE");
    rsi_session_t s;
    rsi_session_init(&s);
    trit r = rsi_trit_guard(&s, 0.0);
    ASSERT(r == TRIT_UNKNOWN, "beauty=0.0 => UNKNOWN, not FALSE");
    ASSERT(r != TRIT_FALSE, "UNKNOWN != FALSE");
    ASSERT(r != TRIT_TRUE, "UNKNOWN != TRUE");
    PASS();
}

/* 6250: Trit values are distinct: F != U != T */
static void test_6250(void)
{
    TEST("Trit values F, U, T are all distinct");
    ASSERT(TRIT_FALSE != TRIT_UNKNOWN, "F != U");
    ASSERT(TRIT_UNKNOWN != TRIT_TRUE, "U != T");
    ASSERT(TRIT_FALSE != TRIT_TRUE, "F != T");
    ASSERT(TRIT_FALSE == -1, "F == -1");
    ASSERT(TRIT_UNKNOWN == 0, "U == 0");
    ASSERT(TRIT_TRUE == 1, "T == +1");
    PASS();
}

/* 6251: End-to-end RSI session lifecycle */
static void test_6251(void)
{
    TEST("End-to-end RSI session lifecycle");
    rsi_session_t s;
    int rc = rsi_session_init(&s);
    ASSERT(rc == 0, "init OK");
    ASSERT(rsi_can_continue(&s) == 1, "can continue at start");

    /* Phase 1: 3 approved mutations */
    for (int i = 0; i < 3; i++)
    {
        trit r = rsi_propose_mutation(&s, 0.95, 0.7);
        ASSERT(r == TRIT_TRUE, "Phase 1: approved");
    }
    ASSERT(s.iteration == 3, "3 iterations");
    ASSERT(s.mutations_applied == 3, "3 applied");

    /* Phase 2: 1 rejected mutation */
    trit r2 = rsi_propose_mutation(&s, -0.5, 0.7);
    ASSERT(r2 == TRIT_FALSE, "Phase 2: rejected");
    ASSERT(s.mutations_rejected == 1, "1 rejected");
    ASSERT(s.iteration == 3, "iteration unchanged on reject");

    /* Phase 3: 1 uncertain mutation (low beauty) */
    trit r3 = rsi_propose_mutation(&s, 0.5, 0.7);
    ASSERT(r3 == TRIT_UNKNOWN, "Phase 3: uncertain");
    ASSERT(s.human_queries == 1, "1 human query");

    /* Phase 4: exhaust remaining 7 mutations */
    for (int i = 0; i < 7; i++)
    {
        trit r = rsi_propose_mutation(&s, 0.92, 0.6);
        ASSERT(r == TRIT_TRUE, "Phase 4: approved");
    }
    ASSERT(s.iteration == 10, "10 total iterations");
    ASSERT(rsi_can_continue(&s) == 0, "cannot continue at max");

    /* Phase 5: final attempt blocked */
    trit r5 = rsi_propose_mutation(&s, 0.99, 0.9);
    ASSERT(r5 == TRIT_FALSE, "Phase 5: blocked at cap");
    ASSERT(s.mutations_rejected == 2, "2 total rejected");

    /* Check final eudaimonia */
    double expected_eud = 0.92 * 0.6;
    ASSERT(fabs(s.eudaimonia - expected_eud) < 1e-9, "final eudaimonia");
    PASS();
}

/*--- main -------------------------------------------------------------------*/

int main(void)
{
    printf("\n=== Batch 109: RSI Flywheel Safety & Bounded Iteration ===\n\n");

    test_6202();
    test_6203();
    test_6204();
    test_6205();
    test_6206();
    test_6207();
    test_6208();
    test_6209();
    test_6210();
    test_6211();
    test_6212();
    test_6213();
    test_6214();
    test_6215();
    test_6216();
    test_6217();
    test_6218();
    test_6219();
    test_6220();
    test_6221();
    test_6222();
    test_6223();
    test_6224();
    test_6225();
    test_6226();
    test_6227();
    test_6228();
    test_6229();
    test_6230();
    test_6231();
    test_6232();
    test_6233();
    test_6234();
    test_6235();
    test_6236();
    test_6237();
    test_6238();
    test_6239();
    test_6240();
    test_6241();
    test_6242();
    test_6243();
    test_6244();
    test_6245();
    test_6246();
    test_6247();
    test_6248();
    test_6249();
    test_6250();
    test_6251();

    printf("\n=== Results: %d/%d passed, %d failed ===\n", pass_count, test_count, fail_count);
    return (fail_count == 0) ? 0 : 1;
}
