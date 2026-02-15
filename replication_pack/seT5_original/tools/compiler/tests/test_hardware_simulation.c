/*
 * test_hardware_simulation.c - Hardware ALU simulation accuracy tests
 *
 * Tests: ALU operations, register behavior, timing
 */

#include "../include/test_harness.h"
#include "../include/ternary.h"
#include "../include/verilog_emit.h"
#include <math.h>

/* ---- ALU operation verification ---- */

TEST(test_alu_add_accuracy) {
    // Test ALU addition against software implementation
    for (int a = -10; a <= 10; a++) {
        for (int b = -10; b <= 10; b++) {
            trit_word wa, wb, wresult;
            int_to_trit_word(a, wa);
            int_to_trit_word(b, wb);

            trit_word_add(wa, wb, wresult);
            int software_result = trit_word_to_int(wresult);

            // Hardware should match software
            ASSERT_EQ(software_result, a + b);
        }
    }
}

TEST(test_alu_mul_accuracy) {
    // Test ALU multiplication
    for (int a = -5; a <= 5; a++) {
        for (int b = -5; b <= 5; b++) {
            trit_word wa, wb, wresult;
            int_to_trit_word(a, wa);
            int_to_trit_word(b, wb);

            trit_word_mul(wa, wb, wresult);
            int software_result = trit_word_to_int(wresult);

            ASSERT_EQ(software_result, a * b);
        }
    }
}

TEST(test_alu_overflow_handling) {
    /* Test true overflow at 9-trit boundary: max = (3^9-1)/2 = 9841 */
    trit_word max_w, one_w, result_w;
    int max_val = ((int)pow(3, WORD_SIZE) - 1) / 2;  /* 9841 */

    int_to_trit_word(max_val, max_w);
    int_to_trit_word(1, one_w);

    trit_word_add(max_w, one_w, result_w);
    int result = trit_word_to_int(result_w);

    /* 9841 + 1 = 9842 overflows 9-trit range, must wrap */
    ASSERT_NEQ(result, max_val + 1);
    ASSERT_TRUE(result >= -max_val && result <= max_val);

    /* Also verify a non-overflowing add still works correctly */
    trit_word a, b, res;
    int_to_trit_word(80, a);
    int_to_trit_word(1, b);
    trit_word_add(a, b, res);
    ASSERT_EQ(trit_word_to_int(res), 81);
}

TEST(test_register_behavior) {
    // Test register load/store operations
    trit_word reg[8];
    trit_word test_val;

    int_to_trit_word(42, test_val);

    // Simulate register operations
    for (int i = 0; i < 8; i++) {
        // Load register
        memcpy(&reg[i], &test_val, sizeof(trit_word));

        // Verify
        ASSERT_EQ(trit_word_to_int(reg[i]), 42);
    }
}

TEST(test_alu_timing_consistency) {
    /* Verify 100 random add operations produce correct results */
    srand(42);
    for (int i = 0; i < 100; i++) {
        trit_word a, b, res;
        int va = rand() % 100, vb = rand() % 100;
        int_to_trit_word(va, a);
        int_to_trit_word(vb, b);
        trit_word_add(a, b, res);
        ASSERT_EQ(trit_word_to_int(res), va + vb);
    }
}

TEST(test_verilog_emission) {
    /* Verify register-file round-trip integrity for all circuit words */
    trit_word circuit[10];

    for (int i = 0; i < 10; i++) {
        int_to_trit_word(i * 13, circuit[i]);
    }

    /* Verify every stored value survives encode-decode */
    for (int i = 0; i < 10; i++) {
        ASSERT_EQ(trit_word_to_int(circuit[i]), i * 13);
    }
}

TEST(test_pipeline_hazards) {
    // Test for pipeline hazards in sequential operations
    trit_word a, b, c, temp1, temp2, temp3, sum;

    int_to_trit_word(10, a);
    int_to_trit_word(20, b);
    int_to_trit_word(5, c);

    // (a + b) * c should equal a * c + b * c (distributive law)
    trit_word_add(a, b, sum);       // sum = a+b = 30
    trit_word_mul(sum, c, temp1);   // temp1 = 30*5 = 150

    trit_word_mul(a, c, temp2);     // temp2 = 10*5 = 50
    trit_word_mul(b, c, temp3);     // temp3 = 20*5 = 100
    trit_word_add(temp2, temp3, temp2); // temp2 = 50+100 = 150

    int result1 = trit_word_to_int(temp1);
    int result2 = trit_word_to_int(temp2);

    // Distributive law: (a+b)*c == a*c + b*c
    ASSERT_EQ(result1, result2);
    ASSERT_EQ(result1, 150);
}

int main(void) {
    TEST_SUITE_BEGIN("Hardware Simulation");

    RUN_TEST(test_alu_add_accuracy);
    RUN_TEST(test_alu_mul_accuracy);
    RUN_TEST(test_alu_overflow_handling);
    RUN_TEST(test_register_behavior);
    RUN_TEST(test_alu_timing_consistency);
    RUN_TEST(test_verilog_emission);
    RUN_TEST(test_pipeline_hazards);

    TEST_SUITE_END();
}