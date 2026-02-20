/*
 * test_linker.c - Linker tests (Phase 3)
 * Tests symbol resolution, relocation, multi-module linking,
 * and error detection.
 */

#include <stdio.h>
#include <string.h>
#include "../include/test_harness.h"
#include "../include/linker.h"
#include "../include/vm.h"

/* === Basic module management === */

TEST(test_linker_init) {
    Linker lnk;
    linker_init(&lnk);
    ASSERT_EQ(lnk.module_count, 0);
    ASSERT_EQ(lnk.global_count, 0);
    ASSERT_EQ(lnk.error_count, 0);
}

TEST(test_add_module) {
    Linker lnk;
    linker_init(&lnk);
    unsigned char code[] = {OP_PUSH, 42, OP_HALT};
    int id = linker_add_module(&lnk, code, 3);
    ASSERT_EQ(id, 0);
    ASSERT_EQ(lnk.module_count, 1);
    ASSERT_EQ(lnk.modules[0].code_len, 3);
}

TEST(test_add_multiple_modules) {
    Linker lnk;
    linker_init(&lnk);
    unsigned char code1[] = {OP_PUSH, 1};
    unsigned char code2[] = {OP_PUSH, 2, OP_ADD, OP_HALT};
    int id1 = linker_add_module(&lnk, code1, 2);
    int id2 = linker_add_module(&lnk, code2, 4);
    ASSERT_EQ(id1, 0);
    ASSERT_EQ(id2, 1);
    ASSERT_EQ(lnk.module_count, 2);
}

/* === Symbol management === */

TEST(test_add_export_symbol) {
    Linker lnk;
    linker_init(&lnk);
    unsigned char code[] = {OP_PUSH, 1, OP_HALT};
    int id = linker_add_module(&lnk, code, 3);
    int rc = linker_add_symbol(&lnk, id, "main", 0, SYM_EXPORT);
    ASSERT_EQ(rc, 0);
    ASSERT_EQ(lnk.modules[0].sym_count, 1);
}

TEST(test_add_import_symbol) {
    Linker lnk;
    linker_init(&lnk);
    unsigned char code[] = {OP_CALL, 0};
    int id = linker_add_module(&lnk, code, 2);
    linker_add_symbol(&lnk, id, "helper", 0, SYM_IMPORT);
    ASSERT_EQ(lnk.modules[0].sym_count, 1);
    ASSERT_EQ(lnk.modules[0].symbols[0].vis, SYM_IMPORT);
}

/* === Single-module linking === */

TEST(test_link_single_module) {
    Linker lnk;
    linker_init(&lnk);
    unsigned char code[] = {OP_PUSH, 7, OP_HALT};
    int id = linker_add_module(&lnk, code, 3);
    linker_add_symbol(&lnk, id, "main", 0, SYM_EXPORT);

    int errs = linker_link(&lnk);
    ASSERT_EQ(errs, 0);
    ASSERT_EQ(lnk.output_len, 3);

    /* Run the linked output */
    vm_memory_reset();
    vm_run(lnk.output, (size_t)lnk.output_len);
    ASSERT_EQ(vm_get_result(), 7);
}

/* === Multi-module linking === */

TEST(test_link_two_modules) {
    Linker lnk;
    linker_init(&lnk);

    /* Module 0: PUSH 3 */
    unsigned char code1[] = {OP_PUSH, 3};
    int m0 = linker_add_module(&lnk, code1, 2);
    linker_add_symbol(&lnk, m0, "init", 0, SYM_EXPORT);

    /* Module 1: PUSH 4, ADD, HALT */
    unsigned char code2[] = {OP_PUSH, 4, OP_ADD, OP_HALT};
    int m1 = linker_add_module(&lnk, code2, 4);
    linker_add_symbol(&lnk, m1, "compute", 0, SYM_EXPORT);

    int errs = linker_link(&lnk);
    ASSERT_EQ(errs, 0);
    ASSERT_EQ(lnk.output_len, 6); /* 2 + 4 */

    /* Run: should push 3, push 4, add, halt -> 7 */
    vm_memory_reset();
    vm_run(lnk.output, (size_t)lnk.output_len);
    ASSERT_EQ(vm_get_result(), 7);
}

/* === Relocation === */

TEST(test_relocation_patches_call) {
    Linker lnk;
    linker_init(&lnk);

    /* Module 0: PUSH 5, CALL <target>, HALT
     * target byte initially 0, should be patched to module 1 start */
    unsigned char code1[] = {OP_PUSH, 5, OP_CALL, 0, OP_HALT};
    int m0 = linker_add_module(&lnk, code1, 5);
    linker_add_symbol(&lnk, m0, "main", 0, SYM_EXPORT);
    linker_add_reloc(&lnk, m0, 3, "helper"); /* byte at offset 3 = target */

    /* Module 1: RET (just return) */
    unsigned char code2[] = {OP_RET};
    int m1 = linker_add_module(&lnk, code2, 1);
    linker_add_symbol(&lnk, m1, "helper", 0, SYM_EXPORT);

    int errs = linker_link(&lnk);
    ASSERT_EQ(errs, 0);

    /* Check that the CALL target was patched to module 1's base */
    ASSERT_EQ(lnk.output[3], 5); /* helper at offset 5 */
}

/* === Error detection === */

TEST(test_duplicate_symbol_error) {
    Linker lnk;
    linker_init(&lnk);

    unsigned char code[] = {OP_HALT};
    int m0 = linker_add_module(&lnk, code, 1);
    int m1 = linker_add_module(&lnk, code, 1);
    linker_add_symbol(&lnk, m0, "main", 0, SYM_EXPORT);
    linker_add_symbol(&lnk, m1, "main", 0, SYM_EXPORT);

    int errs = linker_link(&lnk);
    ASSERT_TRUE(errs >= 1); /* duplicate 'main' */
}

TEST(test_undefined_symbol_error) {
    Linker lnk;
    linker_init(&lnk);

    unsigned char code[] = {OP_CALL, 0, OP_HALT};
    int m0 = linker_add_module(&lnk, code, 3);
    linker_add_reloc(&lnk, m0, 1, "nonexistent");

    int errs = linker_link(&lnk);
    ASSERT_TRUE(errs >= 1); /* undefined symbol */
}

TEST(test_unresolved_import_error) {
    Linker lnk;
    linker_init(&lnk);

    unsigned char code[] = {OP_HALT};
    int m0 = linker_add_module(&lnk, code, 1);
    linker_add_symbol(&lnk, m0, "missing_func", 0, SYM_IMPORT);

    int errs = linker_link(&lnk);
    ASSERT_TRUE(errs >= 1); /* unresolved import */
}

/* === Symbol resolution === */

TEST(test_resolve_after_link) {
    Linker lnk;
    linker_init(&lnk);

    unsigned char code1[] = {OP_PUSH, 1};
    unsigned char code2[] = {OP_PUSH, 2, OP_HALT};
    int m0 = linker_add_module(&lnk, code1, 2);
    int m1 = linker_add_module(&lnk, code2, 3);
    linker_add_symbol(&lnk, m0, "start", 0, SYM_EXPORT);
    linker_add_symbol(&lnk, m1, "compute", 0, SYM_EXPORT);

    linker_link(&lnk);

    ASSERT_EQ(linker_resolve(&lnk, "start"), 0);
    ASSERT_EQ(linker_resolve(&lnk, "compute"), 2); /* after module 0 */
    ASSERT_EQ(linker_resolve(&lnk, "nope"), -1);
}

/* === Local symbols === */

TEST(test_local_symbol_not_global) {
    Linker lnk;
    linker_init(&lnk);

    unsigned char code[] = {OP_PUSH, 1, OP_HALT};
    int m0 = linker_add_module(&lnk, code, 3);
    linker_add_symbol(&lnk, m0, "internal", 0, SYM_LOCAL);

    linker_link(&lnk);

    /* Local symbols should NOT be in the global table */
    ASSERT_EQ(linker_resolve(&lnk, "internal"), -1);
}

int main(void) {
    TEST_SUITE_BEGIN("Linker");

    RUN_TEST(test_linker_init);
    RUN_TEST(test_add_module);
    RUN_TEST(test_add_multiple_modules);
    RUN_TEST(test_add_export_symbol);
    RUN_TEST(test_add_import_symbol);
    RUN_TEST(test_link_single_module);
    RUN_TEST(test_link_two_modules);
    RUN_TEST(test_relocation_patches_call);
    RUN_TEST(test_duplicate_symbol_error);
    RUN_TEST(test_undefined_symbol_error);
    RUN_TEST(test_unresolved_import_error);
    RUN_TEST(test_resolve_after_link);
    RUN_TEST(test_local_symbol_not_global);

    TEST_SUITE_END();
}
