/*
 * test_harness.h - Lightweight C test framework
 *
 * Zero-dependency test harness for autonomous verification.
 * Provides structured test output, assertion macros, and
 * pass/fail counting for CI integration.
 *
 * Usage:
 *   TEST(my_test) {
 *       ASSERT_EQ(1 + 1, 2);
 *       ASSERT_TRUE(some_condition);
 *   }
 *
 *   int main(void) {
 *       TEST_SUITE_BEGIN("My Suite");
 *       RUN_TEST(my_test);
 *       TEST_SUITE_END();
 *   }
 */

#ifndef TEST_HARNESS_H
#define TEST_HARNESS_H

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

/* Global test counters */
static int _th_tests_run    = 0;
static int _th_tests_passed = 0;
static int _th_tests_failed = 0;
static int _th_current_failed = 0;
static const char *_th_suite_name = "Unknown";

/* Define a test function */
#define TEST(name) static void name(void)

/* Run a test function and track results */
#define RUN_TEST(name) do { \
    _th_tests_run++; \
    _th_current_failed = 0; \
    printf("  [RUN ] %s ... ", #name); \
    fflush(stdout); \
    name(); \
    if (_th_current_failed == 0) { \
        _th_tests_passed++; \
        printf("PASS\n"); \
    } else { \
        _th_tests_failed++; \
        printf("FAIL\n"); \
    } \
} while(0)

/* Suite begin/end with summary */
#define TEST_SUITE_BEGIN(suite) do { \
    _th_suite_name = (suite); \
    _th_tests_run = 0; \
    _th_tests_passed = 0; \
    _th_tests_failed = 0; \
    printf("=== Test Suite: %s ===\n", _th_suite_name); \
} while(0)

#define TEST_SUITE_END() do { \
    printf("=== %s: %d/%d passed", _th_suite_name, _th_tests_passed, _th_tests_run); \
    if (_th_tests_failed > 0) { \
        printf(" (%d FAILED)", _th_tests_failed); \
    } \
    printf(" ===\n"); \
    return (_th_tests_failed > 0) ? 1 : 0; \
} while(0)

/* Assertion macros - report file:line on failure but continue the suite */
#define ASSERT_TRUE(cond) do { \
    if (!(cond)) { \
        fprintf(stderr, "\n    ASSERT_TRUE failed: %s\n      at %s:%d\n", \
                #cond, __FILE__, __LINE__); \
        _th_current_failed = 1; \
        return; \
    } \
} while(0)

#define ASSERT_FALSE(cond) do { \
    if ((cond)) { \
        fprintf(stderr, "\n    ASSERT_FALSE failed: %s\n      at %s:%d\n", \
                #cond, __FILE__, __LINE__); \
        _th_current_failed = 1; \
        return; \
    } \
} while(0)

#define ASSERT_EQ(actual, expected) do { \
    long long _a = (long long)(actual); \
    long long _e = (long long)(expected); \
    if (_a != _e) { \
        fprintf(stderr, "\n    ASSERT_EQ failed: %s == %lld, expected %s == %lld\n      at %s:%d\n", \
                #actual, _a, #expected, _e, __FILE__, __LINE__); \
        _th_current_failed = 1; \
        return; \
    } \
} while(0)

#define ASSERT_NEQ(actual, not_expected) do { \
    long long _a = (long long)(actual); \
    long long _ne = (long long)(not_expected); \
    if (_a == _ne) { \
        fprintf(stderr, "\n    ASSERT_NEQ failed: %s == %lld, should not equal %s\n      at %s:%d\n", \
                #actual, _a, #not_expected, __FILE__, __LINE__); \
        _th_current_failed = 1; \
        return; \
    } \
} while(0)

#define ASSERT_STR_EQ(actual, expected) do { \
    const char *_a = (actual); \
    const char *_e = (expected); \
    if (_a == NULL || _e == NULL || strcmp(_a, _e) != 0) { \
        fprintf(stderr, "\n    ASSERT_STR_EQ failed: \"%s\" != \"%s\"\n      at %s:%d\n", \
                _a ? _a : "(null)", _e ? _e : "(null)", __FILE__, __LINE__); \
        _th_current_failed = 1; \
        return; \
    } \
} while(0)

#define ASSERT_NOT_NULL(ptr) do { \
    if ((ptr) == NULL) { \
        fprintf(stderr, "\n    ASSERT_NOT_NULL failed: %s is NULL\n      at %s:%d\n", \
                #ptr, __FILE__, __LINE__); \
        _th_current_failed = 1; \
        return; \
    } \
} while(0)

#define ASSERT_NULL(ptr) do { \
    if ((ptr) != NULL) { \
        fprintf(stderr, "\n    ASSERT_NULL failed: %s is not NULL\n      at %s:%d\n", \
                #ptr, __FILE__, __LINE__); \
        _th_current_failed = 1; \
        return; \
    } \
} while(0)

#define ASSERT_GT(actual, threshold) do { \
    long long _a = (long long)(actual); \
    long long _t = (long long)(threshold); \
    if (!(_a > _t)) { \
        fprintf(stderr, "\n    ASSERT_GT failed: %s == %lld, expected > %lld\n      at %s:%d\n", \
                #actual, _a, _t, __FILE__, __LINE__); \
        _th_current_failed = 1; \
        return; \
    } \
} while(0)

#define ASSERT_LT(actual, threshold) do { \
    long long _a = (long long)(actual); \
    long long _t = (long long)(threshold); \
    if (!(_a < _t)) { \
        fprintf(stderr, "\n    ASSERT_LT failed: %s == %lld, expected < %lld\n      at %s:%d\n", \
                #actual, _a, _t, __FILE__, __LINE__); \
        _th_current_failed = 1; \
        return; \
    } \
} while(0)

#define ASSERT_GE(actual, threshold) do { \
    long long _a = (long long)(actual); \
    long long _t = (long long)(threshold); \
    if (!(_a >= _t)) { \
        fprintf(stderr, "\n    ASSERT_GE failed: %s == %lld, expected >= %lld\n      at %s:%d\n", \
                #actual, _a, _t, __FILE__, __LINE__); \
        _th_current_failed = 1; \
        return; \
    } \
} while(0)

#define ASSERT_LE(actual, threshold) do { \
    long long _a = (long long)(actual); \
    long long _t = (long long)(threshold); \
    if (!(_a <= _t)) { \
        fprintf(stderr, "\n    ASSERT_LE failed: %s == %lld, expected <= %lld\n      at %s:%d\n", \
                #actual, _a, _t, __FILE__, __LINE__); \
        _th_current_failed = 1; \
        return; \
    } \
} while(0)

#endif /* TEST_HARNESS_H */
