/**
 * @file test_modular.c
 * @brief seT6 — LEGO-Like Modularity Test Suite
 *
 * Tests the Arch Linux–inspired modular framework:
 *   - Module registration and lookup
 *   - Dependency management and checking
 *   - Drop-in configuration overrides
 *   - Module load/unload lifecycle
 *   - Radix Integrity Guard (binary creep detection)
 *   - Strip binary emulation
 *
 * Target: 50+ assertions.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "set6/trit.h"
#include "trit_modular.h"

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
/*  Test: Framework Initialization                                          */
/* ======================================================================== */

static void test_init(void) {
    SECTION("Framework Initialization");

    tmod_framework_t fw;

    TEST("Init returns OK");
    ASSERT(tmod_init(&fw) == TMOD_OK, "init failed");

    TEST("Module count starts at 0");
    ASSERT(tmod_count(&fw) == 0, "expected 0 modules");

    TEST("Radix guard starts clean");
    ASSERT(fw.radix_guard.guard_status == TRIT_TRUE, "expected TRIT_TRUE");

    TEST("Init with NULL returns error");
    ASSERT(tmod_init(NULL) == TMOD_ERR_INIT, "expected ERR_INIT");

    TEST("Framework marked initialized");
    ASSERT(fw.initialized == 1, "expected initialized=1");
}

/* ======================================================================== */
/*  Test: Module Registration                                               */
/* ======================================================================== */

static void test_registration(void) {
    SECTION("Module Registration");

    tmod_framework_t fw;
    tmod_init(&fw);

    TEST("Register 'tipc' module");
    int id = tmod_register(&fw, "tipc", TMOD_RADIX_TERNARY);
    ASSERT(id == 0, "expected id 0");

    TEST("Module count is 1");
    ASSERT(tmod_count(&fw) == 1, "expected 1");

    TEST("Register 'tfs' module");
    id = tmod_register(&fw, "tfs", TMOD_RADIX_TERNARY);
    ASSERT(id == 1, "expected id 1");

    TEST("Register 'binary_emu' module (binary)");
    id = tmod_register(&fw, "binary_emu", TMOD_RADIX_BINARY_EMU);
    ASSERT(id == 2, "expected id 2");

    TEST("Module count is 3");
    ASSERT(tmod_count(&fw) == 3, "expected 3");

    TEST("Duplicate registration rejected");
    ASSERT(tmod_register(&fw, "tipc", TMOD_RADIX_TERNARY) == TMOD_ERR_FULL,
           "expected ERR_FULL for duplicate");

    TEST("Find 'tipc' by name");
    tmod_module_t *m = tmod_find(&fw, "tipc");
    ASSERT(m != NULL && m->radix_purity == TMOD_RADIX_TERNARY, "not found or wrong purity");

    TEST("Find non-existent module");
    ASSERT(tmod_find(&fw, "nonexistent") == NULL, "expected NULL");

    TEST("Register with NULL name");
    ASSERT(tmod_register(&fw, NULL, TMOD_RADIX_TERNARY) == TMOD_ERR_INIT,
           "expected ERR_INIT");
}

/* ======================================================================== */
/*  Test: Dependency Management                                             */
/* ======================================================================== */

static void test_dependencies(void) {
    SECTION("Dependency Management");

    tmod_framework_t fw;
    tmod_init(&fw);

    tmod_register(&fw, "core", TMOD_RADIX_TERNARY);
    tmod_register(&fw, "net", TMOD_RADIX_TERNARY);
    tmod_register(&fw, "app", TMOD_RADIX_TERNARY);

    /* core has no deps */
    TEST("Core has no deps — deps satisfied");
    ASSERT(tmod_deps_satisfied(&fw, "core") == 1, "expected satisfied");

    /* net depends on core */
    TEST("Add dep: net -> core");
    ASSERT(tmod_add_dependency(&fw, "net", "core") == TMOD_OK, "add dep failed");

    TEST("Net deps not satisfied (core unloaded)");
    ASSERT(tmod_deps_satisfied(&fw, "net") == 0, "expected not satisfied");

    /* Load core first */
    TEST("Load core");
    ASSERT(tmod_load(&fw, "core") == TMOD_OK, "load core failed");

    TEST("Net deps now satisfied");
    ASSERT(tmod_deps_satisfied(&fw, "net") == 1, "expected satisfied");

    /* app depends on net (which depends on core) */
    TEST("Add dep: app -> net");
    ASSERT(tmod_add_dependency(&fw, "app", "net") == TMOD_OK, "add dep failed");

    TEST("App deps not satisfied (net unloaded)");
    ASSERT(tmod_deps_satisfied(&fw, "app") == 0, "expected not satisfied");

    TEST("Load net");
    ASSERT(tmod_load(&fw, "net") == TMOD_OK, "load net failed");

    TEST("App deps now satisfied");
    ASSERT(tmod_deps_satisfied(&fw, "app") == 1, "expected satisfied");

    TEST("Load app");
    ASSERT(tmod_load(&fw, "app") == TMOD_OK, "load app failed");

    TEST("Dep on non-existent module");
    ASSERT(tmod_add_dependency(&fw, "bogus", "core") == TMOD_ERR_NOTFOUND,
           "expected ERR_NOTFOUND");
}

/* ======================================================================== */
/*  Test: Drop-in Configuration                                             */
/* ======================================================================== */

static void test_configs(void) {
    SECTION("Drop-in Configuration");

    tmod_framework_t fw;
    tmod_init(&fw);
    tmod_register(&fw, "tipc", TMOD_RADIX_TERNARY);

    TEST("Add config: TritPackRatio=5:8");
    ASSERT(tmod_add_config(&fw, "tipc", "TritPackRatio", "5:8") == TMOD_OK,
           "config add failed");

    TEST("Get config: TritPackRatio");
    const char *v = tmod_get_config(&fw, "tipc", "TritPackRatio");
    ASSERT(v != NULL && strcmp(v, "5:8") == 0, "expected 5:8");

    TEST("Add config: MaxTrits=512");
    ASSERT(tmod_add_config(&fw, "tipc", "MaxTrits", "512") == TMOD_OK,
           "config add failed");

    TEST("Override config: TritPackRatio=9:14");
    ASSERT(tmod_add_config(&fw, "tipc", "TritPackRatio", "9:14") == TMOD_OK,
           "override failed");

    TEST("Verify override applied");
    v = tmod_get_config(&fw, "tipc", "TritPackRatio");
    ASSERT(v != NULL && strcmp(v, "9:14") == 0, "expected 9:14 after override");

    TEST("Config for unknown module");
    ASSERT(tmod_add_config(&fw, "bogus", "x", "y") == TMOD_ERR_NOTFOUND,
           "expected ERR_NOTFOUND");

    TEST("Get non-existent config key");
    ASSERT(tmod_get_config(&fw, "tipc", "NoSuchKey") == NULL, "expected NULL");
}

/* ======================================================================== */
/*  Test: Radix Integrity Guard                                             */
/* ======================================================================== */

static void test_radix_guard(void) {
    SECTION("Radix Integrity Guard");

    tmod_framework_t fw;
    tmod_init(&fw);

    tmod_register(&fw, "tipc", TMOD_RADIX_TERNARY);
    tmod_register(&fw, "tfs", TMOD_RADIX_TERNARY);

    TEST("Scan with all ternary — 0 violations");
    int v = tmod_radix_scan(&fw);
    ASSERT(v == 0, "expected 0 violations");

    TEST("Guard status is TRIT_TRUE (clean)");
    ASSERT(fw.radix_guard.guard_status == TRIT_TRUE, "expected clean");

    TEST("Modules cleared == 2");
    ASSERT(fw.radix_guard.modules_cleared == 2, "expected 2 cleared");

    /* Register a binary emu module */
    tmod_register(&fw, "legacy_bin", TMOD_RADIX_BINARY_EMU);

    TEST("Scan with binary creep — 1 violation");
    v = tmod_radix_scan(&fw);
    ASSERT(v == 1, "expected 1 violation");

    TEST("Guard status is TRIT_FALSE (impure)");
    ASSERT(fw.radix_guard.guard_status == TRIT_FALSE, "expected impure");

    TEST("Strip binary emu from legacy_bin");
    ASSERT(tmod_strip_binary_emu(&fw, "legacy_bin") == TMOD_OK, "strip failed");

    TEST("Re-scan — 0 violations after strip");
    v = tmod_radix_scan(&fw);
    ASSERT(v == 0, "expected 0 violations after strip");

    TEST("Guard status clean after strip");
    ASSERT(fw.radix_guard.guard_status == TRIT_TRUE, "expected clean");

    TEST("Scans performed count");
    ASSERT(fw.radix_guard.scans_performed == 3, "expected 3 scans");
}

/* ======================================================================== */
/*  Test: Module Load / Unload Lifecycle                                    */
/* ======================================================================== */

static void test_lifecycle(void) {
    SECTION("Module Load / Unload Lifecycle");

    tmod_framework_t fw;
    tmod_init(&fw);

    tmod_register(&fw, "core", TMOD_RADIX_TERNARY);
    tmod_register(&fw, "net", TMOD_RADIX_TERNARY);
    tmod_add_dependency(&fw, "net", "core");

    TEST("Load net with unmet dep — ERR_DEPENDENCY");
    ASSERT(tmod_load(&fw, "net") == TMOD_ERR_DEPENDENCY, "expected dep error");

    TEST("Net state is FAILED after dep error");
    tmod_module_t *m = tmod_find(&fw, "net");
    ASSERT(m && m->state == TMOD_STATE_FAILED, "expected FAILED");

    TEST("Load core succeeds");
    ASSERT(tmod_load(&fw, "core") == TMOD_OK, "load core failed");

    TEST("Core state is ACTIVE");
    m = tmod_find(&fw, "core");
    ASSERT(m && m->state == TMOD_STATE_ACTIVE, "expected ACTIVE");

    TEST("Load net now succeeds");
    ASSERT(tmod_load(&fw, "net") == TMOD_OK, "load net failed");

    TEST("Unload core");
    ASSERT(tmod_unload(&fw, "core") == TMOD_OK, "unload failed");

    TEST("Core state is UNLOADED after unload");
    m = tmod_find(&fw, "core");
    ASSERT(m && m->state == TMOD_STATE_UNLOADED, "expected UNLOADED");

    TEST("Load non-existent module");
    ASSERT(tmod_load(&fw, "nonexistent") == TMOD_ERR_NOTFOUND,
           "expected ERR_NOTFOUND");
}

/* ======================================================================== */
/*  Main                                                                    */
/* ======================================================================== */

int main(void) {
    printf("\n╔══════════════════════════════════════════════════════════════╗\n");
    printf("║  seT6 LEGO-Like Modularity Test Suite                       ║\n");
    printf("╚══════════════════════════════════════════════════════════════╝\n");

    test_init();
    test_registration();
    test_dependencies();
    test_configs();
    test_radix_guard();
    test_lifecycle();

    printf("\n══════════════════════════════════════════════════════════════\n");
    printf("  Modularity Tests: %d passed, %d failed, %d total\n",
           tests_passed, tests_failed, tests_total);
    printf("══════════════════════════════════════════════════════════════\n");

    return tests_failed > 0 ? 1 : 0;
}
