/*
 * test_sel4_verify.c - Tests for TASK-019: Full seL4 Compile/Verify
 *
 * Tests: capability derivation trees, endpoint IPC, thread control,
 * full compilation pipeline, invariant verification.
 */

#include "../include/test_harness.h"
#include "../include/sel4_verify.h"
#include "../include/vm.h"

/* ---- Capability tree tests ---- */

TEST(test_cap_tree_create) {
    CapNode *root = cap_tree_root(1, OBJ_ENDPOINT);
    ASSERT_NOT_NULL(root);
    ASSERT_EQ(root->cap.object_id, 1);
    ASSERT_EQ(root->cap.rights, CAP_RIGHT_ALL);
    ASSERT_EQ(root->child_count, 0);
    ASSERT_EQ(root->obj_type, OBJ_ENDPOINT);
    cap_tree_free(root);
}

TEST(test_cap_derive_single) {
    CapNode *root = cap_tree_root(1, OBJ_MEMORY);
    CapNode *child = cap_derive(root, CAP_RIGHT_READ);
    ASSERT_NOT_NULL(child);
    ASSERT_EQ(child->cap.object_id, 1);
    ASSERT_EQ(child->cap.rights, CAP_RIGHT_READ);
    ASSERT_EQ(child->parent, root);
    ASSERT_EQ(root->child_count, 1);
    cap_tree_free(root);
}

TEST(test_cap_derive_ternary_branching) {
    CapNode *root = cap_tree_root(1, OBJ_CNODE);
    CapNode *c1 = cap_derive(root, CAP_RIGHT_READ);
    CapNode *c2 = cap_derive(root, CAP_RIGHT_WRITE);
    CapNode *c3 = cap_derive(root, CAP_RIGHT_GRANT);
    ASSERT_NOT_NULL(c1);
    ASSERT_NOT_NULL(c2);
    ASSERT_NOT_NULL(c3);
    ASSERT_EQ(root->child_count, 3);
    /* Fourth derivation should fail (max 3 children) */
    CapNode *c4 = cap_derive(root, CAP_RIGHT_ALL);
    ASSERT_NULL(c4);
    cap_tree_free(root);
}

TEST(test_cap_no_escalation) {
    CapNode *root = cap_tree_root(1, OBJ_ENDPOINT);
    cap_derive(root, CAP_RIGHT_READ);
    cap_derive(root, CAP_RIGHT_READ | CAP_RIGHT_WRITE);
    ASSERT_TRUE(verify_no_escalation(root));
    cap_tree_free(root);
}

TEST(test_cap_revoke_tree) {
    CapNode *root = cap_tree_root(1, OBJ_ENDPOINT);
    CapNode *c1 = cap_derive(root, CAP_RIGHT_ALL);
    cap_derive(c1, CAP_RIGHT_READ);
    cap_derive(c1, CAP_RIGHT_WRITE);

    ASSERT_EQ(cap_tree_count(root), 4);

    /* Revoke c1 — should revoke c1 and its children */
    cap_revoke_tree(c1);
    ASSERT_EQ(c1->cap.rights, 0);
    ASSERT_TRUE(verify_revocation(c1));

    /* Root should still have rights */
    ASSERT_EQ(root->cap.rights, CAP_RIGHT_ALL);

    cap_tree_free(root);
}

TEST(test_cap_tree_count) {
    CapNode *root = cap_tree_root(1, OBJ_MEMORY);
    cap_derive(root, CAP_RIGHT_READ);
    CapNode *c2 = cap_derive(root, CAP_RIGHT_WRITE);
    cap_derive(c2, CAP_RIGHT_READ);
    ASSERT_EQ(cap_tree_count(root), 4);
    cap_tree_free(root);
}

/* ---- Endpoint IPC tests ---- */

TEST(test_endpoint_init) {
    seL4_Endpoint ep;
    endpoint_init(&ep, 42);
    ASSERT_EQ(ep.ep_id, 42);
    ASSERT_EQ(ep.msg_count, 0);
    ASSERT_EQ(ep.cap.rights, CAP_RIGHT_ALL);
}

TEST(test_endpoint_send_recv) {
    seL4_Endpoint ep;
    endpoint_init(&ep, 1);
    ASSERT_EQ(endpoint_send(&ep, 100), 0);
    ASSERT_EQ(endpoint_send(&ep, 200), 0);
    ASSERT_EQ(ep.msg_count, 2);

    int msg = 0;
    ASSERT_EQ(endpoint_recv(&ep, &msg), 0);
    ASSERT_EQ(msg, 100);
    ASSERT_EQ(endpoint_recv(&ep, &msg), 0);
    ASSERT_EQ(msg, 200);
    ASSERT_EQ(ep.msg_count, 0);
}

TEST(test_endpoint_full) {
    seL4_Endpoint ep;
    endpoint_init(&ep, 1);
    for (int i = 0; i < 9; i++) {
        ASSERT_EQ(endpoint_send(&ep, i), 0);
    }
    /* Queue full — should return -1 */
    ASSERT_EQ(endpoint_send(&ep, 99), -1);
}

TEST(test_endpoint_empty) {
    seL4_Endpoint ep;
    endpoint_init(&ep, 1);
    int msg = 0;
    /* Queue empty — should return -1 */
    ASSERT_EQ(endpoint_recv(&ep, &msg), -1);
}

/* ---- Thread control tests ---- */

TEST(test_tcb_init) {
    seL4_TCB tcb;
    tcb_init(&tcb, 1, 0x100, 0x200);
    ASSERT_EQ(tcb.tid, 1);
    ASSERT_EQ(tcb.priority, 0);
    ASSERT_EQ(tcb.entry_addr, 0x100);
    ASSERT_EQ(tcb.stack_addr, 0x200);
    ASSERT_EQ(tcb.state, 0); /* ready */
}

TEST(test_tcb_multiple) {
    seL4_TCB threads[3];
    for (int i = 0; i < 3; i++) {
        tcb_init(&threads[i], i, i * 100, 0x300 + i * 64);
    }
    ASSERT_EQ(threads[0].tid, 0);
    ASSERT_EQ(threads[1].entry_addr, 100);
    ASSERT_EQ(threads[2].stack_addr, 0x300 + 128);
}

/* ---- Full compile pipeline tests ---- */

TEST(test_sel4_compile_simple_expr) {
    unsigned char code[256];
    int len = sel4_compile_full("1 + 2", code, 256);
    ASSERT_TRUE(len > 0);
    /* Run the compiled bytecode */
    vm_memory_reset();
    vm_run(code, (size_t)len);
    /* Should print "Result: 3" */
}

TEST(test_sel4_compile_cap_arithmetic) {
    unsigned char code[256];
    /* Simulate cap arithmetic: object_id(1) + rights(7) = 8 */
    int len = sel4_compile_full("1 + 7", code, 256);
    ASSERT_TRUE(len > 0);
    vm_memory_reset();
    vm_run(code, (size_t)len);
}

TEST(test_sel4_compile_mul_chain) {
    unsigned char code[256];
    int len = sel4_compile_full("3 * 3 * 3", code, 256);
    ASSERT_TRUE(len > 0);
    vm_memory_reset();
    vm_run(code, (size_t)len);
    /* Should print "Result: 27" (3^3 — a ternary power) */
}

/* ---- Verification invariant tests ---- */

TEST(test_verify_escalation_holds) {
    CapNode *root = cap_tree_root(1, OBJ_ENDPOINT);
    CapNode *c1 = cap_derive(root, CAP_RIGHT_READ);
    cap_derive(c1, CAP_RIGHT_READ);
    ASSERT_TRUE(verify_no_escalation(root));
    cap_tree_free(root);
}

TEST(test_verify_revocation_holds) {
    CapNode *root = cap_tree_root(1, OBJ_ENDPOINT);
    CapNode *c1 = cap_derive(root, CAP_RIGHT_ALL);
    CapNode *c2 = cap_derive(c1, CAP_RIGHT_READ);
    (void)c2;
    cap_revoke_tree(c1);
    ASSERT_TRUE(verify_revocation(root));
    cap_tree_free(root);
}

TEST(test_verify_full_tree) {
    /* Build a multi-level tree and verify all invariants */
    CapNode *root = cap_tree_root(1, OBJ_CNODE);
    CapNode *ep = cap_derive(root, CAP_RIGHT_ALL);
    CapNode *mem = cap_derive(root, CAP_RIGHT_READ | CAP_RIGHT_WRITE);
    CapNode *thr = cap_derive(root, CAP_RIGHT_READ);

    /* Second level */
    cap_derive(ep, CAP_RIGHT_READ);
    cap_derive(mem, CAP_RIGHT_READ);
    (void)thr;

    /* root + ep + mem + thr + ep_child + mem_child = 6 */
    ASSERT_EQ(cap_tree_count(root), 6);
    ASSERT_TRUE(verify_no_escalation(root));

    /* Revoke memory subtree */
    cap_revoke_tree(mem);
    ASSERT_TRUE(verify_revocation(root));

    /* Root and ep subtree still have rights */
    ASSERT_EQ(root->cap.rights, CAP_RIGHT_ALL);
    ASSERT_EQ(ep->cap.rights, CAP_RIGHT_ALL);
    ASSERT_EQ(mem->cap.rights, 0);

    cap_tree_free(root);
}

int main(void) {
    TEST_SUITE_BEGIN("seL4 Verify (TASK-019)");
    /* Capability tree */
    RUN_TEST(test_cap_tree_create);
    RUN_TEST(test_cap_derive_single);
    RUN_TEST(test_cap_derive_ternary_branching);
    RUN_TEST(test_cap_no_escalation);
    RUN_TEST(test_cap_revoke_tree);
    RUN_TEST(test_cap_tree_count);
    /* Endpoints */
    RUN_TEST(test_endpoint_init);
    RUN_TEST(test_endpoint_send_recv);
    RUN_TEST(test_endpoint_full);
    RUN_TEST(test_endpoint_empty);
    /* Thread control */
    RUN_TEST(test_tcb_init);
    RUN_TEST(test_tcb_multiple);
    /* Compile pipeline */
    RUN_TEST(test_sel4_compile_simple_expr);
    RUN_TEST(test_sel4_compile_cap_arithmetic);
    RUN_TEST(test_sel4_compile_mul_chain);
    /* Verification */
    RUN_TEST(test_verify_escalation_holds);
    RUN_TEST(test_verify_revocation_holds);
    RUN_TEST(test_verify_full_tree);
    TEST_SUITE_END();
}
