/**
 * @file init.c
 * @brief seT6 Kernel Init — Bootstrap for Balanced Ternary Microkernel
 *
 * Initialises all kernel subsystems via the unified kernel_state_t:
 *   - Memory manager (Unknown-init pages, scrub-on-free)
 *   - IPC (endpoints + notifications, synchronous + async)
 *   - Scheduler (trit-priority, 3-level + round-robin)
 *   - Capability table (grant monotonicity, ternary validity)
 *   - Two-stack model (operand + return)
 *
 * Also used as the primary integration test: exercises every subsystem
 * and reports pass/fail for each check.
 *
 * Build (native test):  make set6_native
 * Build (ternary):      make build-set6
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include "set6/trit.h"
#include "set6/trit_type.h"
#include "set6/trit_emu.h"
#include "set6/trit_cast.h"
#include "set6/syscall.h"
#include "set6/multiradix.h"
#include "set6/wcet.h"
#include "set6/qemu_trit.h"

/* ---- Test harness ----------------------------------------------------- */

static int tests_run    = 0;
static int tests_passed = 0;
static int tests_failed = 0;

#define CHECK(desc, expr) do { \
    tests_run++; \
    if (expr) { \
        tests_passed++; \
        printf("  [PASS] %s\n", desc); \
    } else { \
        tests_failed++; \
        printf("  [FAIL] %s\n", desc); \
    } \
} while(0)

/* ---- Ternary Increment (postfix style, Huawei CN119652311A) ----------- */

static trit trit_inc(trit v) {
    if (v == TRIT_FALSE)   return TRIT_UNKNOWN;
    if (v == TRIT_UNKNOWN) return TRIT_TRUE;
    return TRIT_FALSE;  /* +1 → -1 (wrap) */
}

/* ==== Kernel Init ====================================================== */

void set6_init(void) {
    kernel_state_t ks;
    printf("seT6: initialising...\n\n");

    /* ==== 1. Full kernel init ========================================== */
    printf("--- Kernel Init ---\n");
    kernel_init(&ks, 32);  /* 32 physical pages */

    int total, free_pg, alloc;
    mem_stats(&ks.mem, &total, &free_pg, &alloc);
    CHECK("mem_init: 32 pages total",       total == 32);
    CHECK("mem_init: 32 pages free",        free_pg == 32);
    CHECK("mem_init: 0 pages allocated",    alloc == 0);

    /* ==== 2. Memory manager ============================================ */
    printf("\n--- Memory Manager ---\n");

    int pg0 = mem_alloc(&ks.mem, -1);  /* kernel page */
    int pg1 = mem_alloc(&ks.mem, 0);   /* thread 0's page */
    CHECK("mem_alloc: pg0 >= 0",            pg0 >= 0);
    CHECK("mem_alloc: pg1 >= 0",            pg1 >= 0);
    CHECK("mem_alloc: pg0 != pg1",          pg0 != pg1);

    mem_stats(&ks.mem, &total, &free_pg, &alloc);
    CHECK("mem_stats: 30 free after 2 allocs", free_pg == 30);
    CHECK("mem_stats: 2 allocated",             alloc == 2);

    /* Unknown-init guarantee */
    trit v = mem_read(&ks.mem, pg0, 0);
    CHECK("mem_read: freshly allocated = Unknown", v == TRIT_UNKNOWN);

    /* Write and read back */
    int wr = mem_write(&ks.mem, pg0, 42, TRIT_TRUE);
    CHECK("mem_write: succeeds on allocated page", wr == 0);
    v = mem_read(&ks.mem, pg0, 42);
    CHECK("mem_read: reads back True", v == TRIT_TRUE);

    /* Read-only page */
    ks.mem.pages[pg1].flags = PAGE_FLAG_READONLY;
    wr = mem_write(&ks.mem, pg1, 0, TRIT_TRUE);
    CHECK("mem_write: fails on read-only page", wr == -1);
    ks.mem.pages[pg1].flags = PAGE_FLAG_NONE;

    /* Free with scrub */
    int fr = mem_free(&ks.mem, pg1);
    CHECK("mem_free: succeeds", fr == 0);
    v = mem_read(&ks.mem, pg1, 0);
    CHECK("mem_free: scrubbed (reads Unknown from freed)", v == TRIT_UNKNOWN);

    mem_stats(&ks.mem, &total, &free_pg, &alloc);
    CHECK("mem_stats: 31 free after free", free_pg == 31);

    /* Double-free protection */
    fr = mem_free(&ks.mem, pg1);
    CHECK("mem_free: double-free returns -1", fr == -1);

    /* Reserve */
    int rsv = mem_reserve(&ks.mem, 30);
    CHECK("mem_reserve: succeeds", rsv == 0);
    int pg_rsv = mem_alloc(&ks.mem, -1);
    /* Page 30 is reserved, so next alloc should skip it */
    CHECK("mem_alloc: does not return reserved page", pg_rsv != 30);

    /* ==== 3. Capability table ========================================== */
    printf("\n--- Capabilities ---\n");

    int root = kernel_cap_create(&ks, 0, 7, 0);  /* R|W|G */
    CHECK("cap_create: root cap >= 0",      root >= 0);
    CHECK("cap_check: root has READ",       kernel_cap_check(&ks, root, 1));
    CHECK("cap_check: root has WRITE",      kernel_cap_check(&ks, root, 2));
    CHECK("cap_check: root has GRANT",      kernel_cap_check(&ks, root, 4));

    /* Grant: derive read-only */
    int ro = kernel_cap_grant(&ks, root, 1);  /* only READ */
    CHECK("cap_grant: ro cap >= 0",         ro >= 0);
    CHECK("cap_check: ro has READ",         kernel_cap_check(&ks, ro, 1));
    CHECK("cap_check: ro denies WRITE",     !kernel_cap_check(&ks, ro, 2));
    CHECK("cap_check: ro denies GRANT",     !kernel_cap_check(&ks, ro, 4));

    /* Revoke */
    int rv = kernel_cap_revoke(&ks, ro);
    CHECK("cap_revoke: succeeds",           rv == 0);
    CHECK("cap_check: revoked denies READ", !kernel_cap_check(&ks, ro, 1));

    /* ==== 4. Scheduler ================================================= */
    printf("\n--- Scheduler ---\n");

    syscall_result_t sr;
    sr = syscall_dispatch(&ks, SYSCALL_THREAD_CREATE, 0x100, +1);
    CHECK("thread_create: high prio tid >= 0", sr.retval >= 0);
    int tid_hi = sr.retval;

    sr = syscall_dispatch(&ks, SYSCALL_THREAD_CREATE, 0x200, 0);
    CHECK("thread_create: normal prio tid >= 0", sr.retval >= 0);

    sr = syscall_dispatch(&ks, SYSCALL_THREAD_CREATE, 0x300, -1);
    CHECK("thread_create: low prio tid >= 0", sr.retval >= 0);

    sr = syscall_dispatch(&ks, SYSCALL_THREAD_YIELD, 0, 0);
    CHECK("yield: picks highest priority",  sr.retval == tid_hi);

    int total_t, ready_t, blocked_t, ctx_sw;
    sched_stats(&ks.sched, &total_t, &ready_t, &blocked_t, &ctx_sw);
    CHECK("sched_stats: 3 threads total",   total_t == 3);
    CHECK("sched_stats: 1 context switch",  ctx_sw == 1);

    /* Block and unblock */
    sched_block(&ks.sched, tid_hi, 0);
    sr = syscall_dispatch(&ks, SYSCALL_THREAD_YIELD, 0, 0);
    CHECK("yield after block: picks next thread", sr.retval != tid_hi);

    sched_unblock(&ks.sched, tid_hi);
    sr = syscall_dispatch(&ks, SYSCALL_THREAD_YIELD, 0, 0);
    CHECK("yield after unblock: picks high prio again", sr.retval == tid_hi);

    /* Priority change */
    sched_set_priority(&ks.sched, tid_hi, TRIT_FALSE);  /* demote */
    sr = syscall_dispatch(&ks, SYSCALL_THREAD_YIELD, 0, 0);
    CHECK("yield after demote: picks different thread", sr.retval != tid_hi);

    /* ==== 5. IPC: Endpoints ============================================ */
    printf("\n--- IPC Endpoints ---\n");

    int ep = ipc_endpoint_create(&ks.ipc);
    CHECK("endpoint_create: ep >= 0", ep >= 0);

    /* Build and send a message */
    ipc_msg_t msg;
    trit payload[3] = { TRIT_TRUE, TRIT_UNKNOWN, TRIT_FALSE };
    ipc_msg_build(&msg, payload, 3, 42, 0);
    CHECK("msg_build: length = 3",        msg.length == 3);
    CHECK("msg_build: badge = 42",        msg.sender_badge == 42);
    CHECK("msg_build: word[0] = True",    msg.words[0] == TRIT_TRUE);
    CHECK("msg_build: word[1] = Unknown", msg.words[1] == TRIT_UNKNOWN);
    CHECK("msg_build: word[2] = False",   msg.words[2] == TRIT_FALSE);

    /* Send with no receiver → blocks */
    int send_r = ipc_send(&ks.ipc, ep, &msg, 0);
    CHECK("ipc_send: blocks (no receiver)", send_r == 1);

    /* Now receive → gets the buffered message */
    ipc_msg_t recv_msg;
    int recv_r = ipc_recv(&ks.ipc, ep, &recv_msg, 1);
    CHECK("ipc_recv: immediate (sender was waiting)", recv_r == 0);
    CHECK("ipc_recv: word[0] = True",     recv_msg.words[0] == TRIT_TRUE);
    CHECK("ipc_recv: badge = 42",         recv_msg.sender_badge == 42);

    /* Recv with no sender → blocks */
    recv_r = ipc_recv(&ks.ipc, ep, &recv_msg, 1);
    CHECK("ipc_recv: blocks (no sender)", recv_r == 1);

    /* Send → immediate delivery (receiver waiting) */
    send_r = ipc_send(&ks.ipc, ep, &msg, 0);
    CHECK("ipc_send: immediate (receiver waiting)", send_r == 0);

    /* Destroy endpoint */
    int ed = ipc_endpoint_destroy(&ks.ipc, ep);
    CHECK("endpoint_destroy: succeeds", ed == 0);
    send_r = ipc_send(&ks.ipc, ep, &msg, 0);
    CHECK("ipc_send: fails on destroyed ep", send_r == -1);

    /* ==== 6. IPC: Notifications ======================================== */
    printf("\n--- IPC Notifications ---\n");

    int notif = ipc_notification_create(&ks.ipc);
    CHECK("notification_create: notif >= 0", notif >= 0);

    /* Wait with no signal → blocks */
    int wait_r = ipc_wait(&ks.ipc, notif, 0);
    CHECK("ipc_wait: blocks (no signal)", wait_r == 1);

    /* Signal */
    int sig_r = ipc_signal(&ks.ipc, notif);
    CHECK("ipc_signal: succeeds", sig_r == 0);

    /* Wait after signal → immediate */
    wait_r = ipc_wait(&ks.ipc, notif, 0);
    CHECK("ipc_wait: immediate (signal pending)", wait_r == 0);

    /* Second wait → blocks again (signal consumed) */
    wait_r = ipc_wait(&ks.ipc, notif, 0);
    CHECK("ipc_wait: blocks (signal consumed)", wait_r == 1);

    /* ==== 7. Syscall integration ======================================= */
    printf("\n--- Syscall Integration ---\n");

    sr = syscall_dispatch(&ks, SYSCALL_MMAP, 0, 0);
    CHECK("MMAP syscall: page >= 0", sr.retval >= 0);
    CHECK("MMAP syscall: result = True", sr.result_trit == TRIT_TRUE);

    sr = syscall_dispatch(&ks, SYSCALL_LOAD_BALANCE, 1, -1);
    CHECK("LOAD_BALANCE: succeeds", sr.retval == 0);

    sr = syscall_dispatch(&ks, SYSCALL_DOT_TRIT, 0, 0);
    CHECK("DOT_TRIT: unknown regs dot = 0", sr.retval == 0);

    sr = syscall_dispatch(&ks, SYSCALL_FFT_STEP, 0, 1);
    CHECK("FFT_STEP syscall: succeeds", sr.retval >= 0);

    sr = syscall_dispatch(&ks, SYSCALL_RADIX_CONV, 0, 42);
    CHECK("RADIX_CONV syscall: converts 42", sr.retval > 0);

    sr = syscall_dispatch(&ks, 99, 0, 0);
    CHECK("Unknown syscall: returns -1", sr.retval == -1);

    /* ==== 8. Stack operations ========================================== */
    printf("\n--- Two-Stack Model ---\n");

    /* Drain any leftover values from syscall tests */
    while (ks.operand_sp > 0) kernel_pop(&ks);

    kernel_push(&ks, TRIT_TRUE);
    kernel_push(&ks, TRIT_FALSE);
    trit popped = kernel_pop(&ks);
    CHECK("stack: pop = False (LIFO)", popped == TRIT_FALSE);
    popped = kernel_pop(&ks);
    CHECK("stack: pop = True (LIFO)", popped == TRIT_TRUE);
    popped = kernel_pop(&ks);
    CHECK("stack: underflow = Unknown", popped == TRIT_UNKNOWN);

    /* Return stack (manual, since kernel_state_t exposes it) */
    ks.return_stack[ks.return_sp++] = 0x42;
    ks.return_stack[ks.return_sp++] = 0xFF;
    int ret = ks.return_stack[--ks.return_sp];
    CHECK("return_stack: pop = 0xFF", ret == 0xFF);
    ret = ks.return_stack[--ks.return_sp];
    CHECK("return_stack: pop = 0x42", ret == 0x42);

    /* ==== 9. Kleene logic sanity ======================================= */
    printf("\n--- Kleene Logic ---\n");

    CHECK("AND(T, U) = U", trit_and(TRIT_TRUE, TRIT_UNKNOWN) == TRIT_UNKNOWN);
    CHECK("AND(T, F) = F", trit_and(TRIT_TRUE, TRIT_FALSE) == TRIT_FALSE);
    CHECK("AND(T, T) = T", trit_and(TRIT_TRUE, TRIT_TRUE) == TRIT_TRUE);
    CHECK("OR(T, U) = T",  trit_or(TRIT_TRUE, TRIT_UNKNOWN) == TRIT_TRUE);
    CHECK("OR(F, U) = U",  trit_or(TRIT_FALSE, TRIT_UNKNOWN) == TRIT_UNKNOWN);
    CHECK("NOT(T) = F",    trit_not(TRIT_TRUE) == TRIT_FALSE);
    CHECK("NOT(F) = T",    trit_not(TRIT_FALSE) == TRIT_TRUE);
    CHECK("NOT(U) = U",    trit_not(TRIT_UNKNOWN) == TRIT_UNKNOWN);

    /* Trit increment (Huawei-style) */
    CHECK("inc(-1) = 0",   trit_inc(TRIT_FALSE) == TRIT_UNKNOWN);
    CHECK("inc(0) = +1",   trit_inc(TRIT_UNKNOWN) == TRIT_TRUE);
    CHECK("inc(+1) = -1",  trit_inc(TRIT_TRUE) == TRIT_FALSE);

    /* ==== 10. SIMD / Packed ops ======================================== */
    printf("\n--- SIMD Packed Ops ---\n");

    trit2_reg32 ra = trit2_reg32_splat(TRIT2_TRUE);
    trit2_reg32 rb = trit2_reg32_splat(TRIT2_UNKNOWN);
    trit2_reg32 rc = trit2_reg32_and(ra, rb);
    CHECK("SIMD AND(T_all, U_all)[0] = U",
          trit2_reg32_get(&rc, 0) == TRIT2_UNKNOWN);

    rc = trit2_reg32_or(ra, rb);
    CHECK("SIMD OR(T_all, U_all)[0] = T",
          trit2_reg32_get(&rc, 0) == TRIT2_TRUE);

    rc = trit2_reg32_not(rb);
    CHECK("SIMD NOT(U_all)[0] = U (fixed point)",
          trit2_reg32_get(&rc, 0) == TRIT2_UNKNOWN);

    rc = trit2_reg32_not(ra);
    CHECK("SIMD NOT(T_all)[0] = F",
          trit2_reg32_get(&rc, 0) == TRIT2_FALSE);

    /* Sparsity */
    int zc = trit2_reg32_zero_count(rb);
    CHECK("zero_count(U_all) = 32", zc == 32);
    CHECK("is_sparse(U_all) = 1",   trit2_reg32_is_sparse(rb));
    CHECK("is_sparse(T_all) = 0",   !trit2_reg32_is_sparse(ra));

    /* Fault detection */
    trit2_reg32 rf = trit2_reg32_splat(TRIT2_TRUE);
    trit2_reg32_set(&rf, 5, TRIT2_FAULT);
    CHECK("has_fault: detects injected fault", trit2_reg32_has_fault(rf));
    CHECK("has_fault: clean register = 0", !trit2_reg32_has_fault(ra));

    /* trit ↔ trit2 bridge */
    CHECK("trit_to_trit2(T) = 0x03", trit_to_trit2(TRIT_TRUE) == TRIT2_TRUE);
    CHECK("trit_to_trit2(U) = 0x01", trit_to_trit2(TRIT_UNKNOWN) == TRIT2_UNKNOWN);
    CHECK("trit_to_trit2(F) = 0x00", trit_to_trit2(TRIT_FALSE) == TRIT2_FALSE);
    CHECK("trit2_to_trit(0x03) = T", trit2_to_trit(TRIT2_TRUE) == TRIT_TRUE);
    CHECK("trit2_to_trit(0x01) = U", trit2_to_trit(TRIT2_UNKNOWN) == TRIT_UNKNOWN);
    CHECK("trit2_to_trit(0x02) = U (fault->safe)", trit2_to_trit(TRIT2_FAULT) == TRIT_UNKNOWN);

    /* ==== 11. DOT_TRIT ================================================= */
    printf("\n--- DOT_TRIT ---\n");

    multiradix_state_t mr;
    multiradix_init(&mr);

    /* All-Unknown dot product = 0 (zero ??? zero) */
    int dp = dot_trit(&mr, 0, 1);
    CHECK("dot_trit: all-unknown = 0", dp == 0);

    /* Set reg 0 = all True (+1), reg 1 = all True (+1) → dot = 32 */
    mr.regs[0] = trit2_reg32_splat(TRIT2_TRUE);
    mr.regs[1] = trit2_reg32_splat(TRIT2_TRUE);
    dp = dot_trit(&mr, 0, 1);
    CHECK("dot_trit: T??T = 32", dp == 32);

    /* reg 0 = all True, reg 1 = all False → dot = -32 */
    mr.regs[1] = trit2_reg32_splat(TRIT2_FALSE);
    dp = dot_trit(&mr, 0, 1);
    CHECK("dot_trit: T??F = -32", dp == -32);

    /* Mixed: reg 0 = True except pos 0 = False → dot = -30 */
    mr.regs[0] = trit2_reg32_splat(TRIT2_TRUE);
    mr.regs[1] = trit2_reg32_splat(TRIT2_FALSE);
    trit2_reg32_set(&mr.regs[0], 0, TRIT2_FALSE);
    dp = dot_trit(&mr, 0, 1);
    /* pos 0: F*F = +1, rest: T*F = -1 each => +1 + (-31) = -30 */
    CHECK("dot_trit: mixed = -30", dp == -30);

    /* Sparse path: reg with >50% Unknown triggers sparsity */
    multiradix_init(&mr);
    mr.regs[0] = trit2_reg32_splat(TRIT2_UNKNOWN);
    trit2_reg32_set(&mr.regs[0], 0, TRIT2_TRUE);
    trit2_reg32_set(&mr.regs[0], 1, TRIT2_TRUE);
    mr.regs[1] = trit2_reg32_splat(TRIT2_TRUE);
    dp = dot_trit(&mr, 0, 1);
    CHECK("dot_trit: sparse path = 2", dp == 2);
    CHECK("dot_trit: sparse_skip > 0", mr.dot_sparse_skip > 0);

    /* N:M structured sparsity (2:4 pattern) */
    multiradix_init(&mr);
    mr.regs[0] = trit2_reg32_splat(TRIT2_TRUE);
    mr.regs[1] = trit2_reg32_splat(TRIT2_TRUE);
    int dps = dot_trit_sparse(&mr, 0, 1, 4, 2);
    /* 32 trits / 4-trit blocks = 8 blocks, 2 kept each = 16 MACs */
    CHECK("dot_trit_sparse: 2:4 = 16", dps == 16);

    /* DOT_TRIT accumulator tracks */
    CHECK("dot_trit: acc = last result", mr.dot_acc == 16);
    CHECK("dot_trit: total_ops > 0", mr.dot_total_ops > 0);

    /* Invalid register index */
    dp = dot_trit(&mr, -1, 0);
    CHECK("dot_trit: invalid reg_a = 0", dp == 0);
    dp = dot_trit(&mr, 0, 99);
    CHECK("dot_trit: invalid reg_b = 0", dp == 0);

    /* ==== 12. FFT_STEP ================================================= */
    printf("\n--- FFT_STEP ---\n");

    multiradix_init(&mr);

    /* Load reg 0: [T, U, F, T, U, F, ...] pattern */
    for (int i = 0; i < 32; i++) {
        trit2 v = (i % 3 == 0) ? TRIT2_TRUE :
                  (i % 3 == 1) ? TRIT2_UNKNOWN : TRIT2_FALSE;
        trit2_reg32_set(&mr.regs[0], i, v);
    }

    int groups = fft_step(&mr, 0, 1, 1);
    CHECK("fft_step: groups > 0", groups > 0);
    CHECK("fft_step: stage incremented", mr.fft_stage == 1);

    /* Output register has valid trits (no faults) */
    CHECK("fft_step: no faults in output", !trit2_reg32_has_fault(mr.regs[1]));

    /* Butterfly preserves cardinality: group of 3 identity check
     * If all inputs are the same trit, butterfly should produce defined outputs */
    multiradix_init(&mr);
    mr.regs[2] = trit2_reg32_splat(TRIT2_TRUE);
    groups = fft_step(&mr, 2, 3, 1);
    CHECK("fft_step: uniform input groups", groups > 0);

    /* Verify butterfly output positions are set */
    trit2 out0 = trit2_reg32_get(&mr.regs[3], 0);
    trit2 out1 = trit2_reg32_get(&mr.regs[3], 1);
    trit2 out2 = trit2_reg32_get(&mr.regs[3], 2);
    CHECK("fft_step: out[0] defined", out0 != TRIT2_FAULT);
    CHECK("fft_step: out[1] defined", out1 != TRIT2_FAULT);
    CHECK("fft_step: out[2] defined", out2 != TRIT2_FAULT);

    /* Multi-stage: run two butterfly stages */
    int g2 = fft_step(&mr, 3, 4, 3);
    CHECK("fft_step: stride=3 groups", g2 >= 0);
    CHECK("fft_step: stage = 2 after two steps", mr.fft_stage == 2);

    /* Invalid registers */
    int bad = fft_step(&mr, -1, 0, 1);
    CHECK("fft_step: bad reg_in = -1", bad == -1);
    bad = fft_step(&mr, 0, 0, 0);
    CHECK("fft_step: stride=0 = -1", bad == -1);

    /* ==== 13. RADIX_CONV =============================================== */
    printf("\n--- RADIX_CONV ---\n");

    multiradix_init(&mr);

    /* Convert 0 */
    int nz = radix_conv_to_ternary(&mr, 0, 0);
    CHECK("radix_conv: 0 → 0 non-zero trits", nz == 0);
    int back = radix_conv_to_binary(&mr, 0, 20);
    CHECK("radix_conv: 0 roundtrip", back == 0);

    /* Convert 1 = (+1) in balanced ternary */
    nz = radix_conv_to_ternary(&mr, 0, 1);
    CHECK("radix_conv: 1 → 1 non-zero trit", nz == 1);
    back = radix_conv_to_binary(&mr, 0, 20);
    CHECK("radix_conv: 1 roundtrip", back == 1);

    /* Convert 42 = 1*27 + 2*9 + 1*3 + 0*1
     * Balanced: ... let's just check roundtrip */
    nz = radix_conv_to_ternary(&mr, 1, 42);
    CHECK("radix_conv: 42 → multiple non-zero", nz > 0);
    back = radix_conv_to_binary(&mr, 1, 20);
    CHECK("radix_conv: 42 roundtrip", back == 42);

    /* Convert negative: -13 */
    nz = radix_conv_to_ternary(&mr, 2, -13);
    CHECK("radix_conv: -13 → non-zero", nz > 0);
    back = radix_conv_to_binary(&mr, 2, 20);
    CHECK("radix_conv: -13 roundtrip", back == -13);

    /* Large value: 729 = 3^6 */
    nz = radix_conv_to_ternary(&mr, 3, 729);
    CHECK("radix_conv: 729 → non-zero", nz > 0);
    back = radix_conv_to_binary(&mr, 3, 20);
    CHECK("radix_conv: 729 roundtrip", back == 729);

    /* Tryte range: -364 to +364 (sum 3^0..3^5) */
    nz = radix_conv_to_ternary(&mr, 4, 364);
    back = radix_conv_to_binary(&mr, 4, 6);
    CHECK("radix_conv: 364 (tryte max) roundtrip", back == 364);

    nz = radix_conv_to_ternary(&mr, 4, -364);
    back = radix_conv_to_binary(&mr, 4, 6);
    CHECK("radix_conv: -364 (tryte min) roundtrip", back == -364);

    /* Invalid register */
    nz = radix_conv_to_ternary(&mr, 99, 42);
    CHECK("radix_conv: bad reg = -1", nz == -1);

    /* ==== 14. TRIT_LB Telemetry ======================================== */
    printf("\n--- TRIT_LB Telemetry ---\n");

    multiradix_init(&mr);

    /* Execute several instructions to build up telemetry */
    mr.regs[0] = trit2_reg32_splat(TRIT2_TRUE);
    mr.regs[1] = trit2_reg32_splat(TRIT2_TRUE);
    dot_trit(&mr, 0, 1);
    dot_trit(&mr, 0, 1);
    dot_trit(&mr, 0, 1);
    fft_step(&mr, 0, 2, 1);

    trit_lb_snapshot_t snap = trit_lb_snapshot(&mr);
    CHECK("trit_lb: total_insns = 4", snap.total_insns == 4);
    CHECK("trit_lb: trit_ratio = 100%", snap.trit_ratio_pct == 100);
    CHECK("trit_lb: affinity = trit core", snap.suggested_affinity == 1);

    /* Record a non-trit instruction to dilute ratio */
    mr.lb_total_insns += 10;  /* simulate 10 binary instructions */
    snap = trit_lb_snapshot(&mr);
    CHECK("trit_lb: diluted ratio < 100%", snap.trit_ratio_pct < 100);

    /* Reset */
    trit_lb_reset(&mr);
    snap = trit_lb_snapshot(&mr);
    CHECK("trit_lb: reset total = 0", snap.total_insns == 0);

    /* Sparse hit tracking */
    multiradix_init(&mr);
    /* Make reg 0 sparse (all Unknown except pos 0) */
    mr.regs[0] = trit2_reg32_splat(TRIT2_UNKNOWN);
    trit2_reg32_set(&mr.regs[0], 0, TRIT2_TRUE);
    mr.regs[1] = trit2_reg32_splat(TRIT2_TRUE);
    dot_trit(&mr, 0, 1);
    snap = trit_lb_snapshot(&mr);
    CHECK("trit_lb: sparse_hits = 1", snap.sparse_ratio_pct > 0);

    /* ==== 15. Additional Edge Cases ==================================== */
    printf("\n--- Edge Cases ---\n");

    /* Memory: allocate all pages */
    kernel_state_t ks2;
    kernel_init(&ks2, 4);
    int p0 = mem_alloc(&ks2.mem, 0);
    int p1 = mem_alloc(&ks2.mem, 0);
    int p2 = mem_alloc(&ks2.mem, 0);
    int p3 = mem_alloc(&ks2.mem, 0);
    CHECK("mem_exhaust: all 4 pages allocated", p0>=0 && p1>=0 && p2>=0 && p3>=0);
    int p4 = mem_alloc(&ks2.mem, 0);
    CHECK("mem_exhaust: 5th alloc fails", p4 == -1);

    /* Capability: grant without GRANT right */
    kernel_init(&ks2, 4);
    int rw_cap = kernel_cap_create(&ks2, 0, 3, 0);  /* R|W only, no G */
    int derived = kernel_cap_grant(&ks2, rw_cap, 1);
    CHECK("cap: grant without G right fails", derived == -1);

    /* Capability: revoke already-revoked */
    int rv2 = kernel_cap_revoke(&ks2, rw_cap);
    CHECK("cap: first revoke succeeds", rv2 == 0);
    rv2 = kernel_cap_revoke(&ks2, rw_cap);
    CHECK("cap: re-revoke succeeds (idempotent)", rv2 == 0);
    CHECK("cap: revoked cap denies read", !kernel_cap_check(&ks2, rw_cap, 1));

    /* Scheduler: destroy thread */
    kernel_init(&ks2, 4);
    int tid = sched_create(&ks2.sched, 0x100, TRIT_TRUE);
    CHECK("sched: create tid >= 0", tid >= 0);
    int dr = sched_destroy(&ks2.sched, tid);
    CHECK("sched: destroy succeeds", dr == 0);
    int dt, rt, bt, cs;
    sched_stats(&ks2.sched, &dt, &rt, &bt, &cs);
    CHECK("sched: 0 ready threads after destroy", rt == 0);

    /* Trit type: checked constructor */
    int fault_flag = 0;
    trit valid_t = trit_checked(1, &fault_flag);
    CHECK("trit_checked(1) = T", valid_t == TRIT_TRUE);
    CHECK("trit_checked(1): no fault", fault_flag == 0);
    trit invalid_t = trit_checked(5, &fault_flag);
    CHECK("trit_checked(5) = U (clamped)", invalid_t == TRIT_UNKNOWN);
    CHECK("trit_checked(5): fault set", fault_flag == 1);

    /* Bulk SIMD: AND bulk correctness */
    trit2_reg32 bulk_a[2], bulk_b[2], bulk_dst[2];
    bulk_a[0] = trit2_reg32_splat(TRIT2_TRUE);
    bulk_a[1] = trit2_reg32_splat(TRIT2_FALSE);
    bulk_b[0] = trit2_reg32_splat(TRIT2_UNKNOWN);
    bulk_b[1] = trit2_reg32_splat(TRIT2_TRUE);
    trit2_reg32_and_bulk(bulk_dst, bulk_a, bulk_b, 2);
    CHECK("bulk AND[0] = U", trit2_reg32_get(&bulk_dst[0], 0) == TRIT2_UNKNOWN);
    CHECK("bulk AND[1] = F", trit2_reg32_get(&bulk_dst[1], 0) == TRIT2_FALSE);

    /* Census */
    trit2_reg32 census_r;
    census_r = trit2_reg32_splat(TRIT2_TRUE);
    trit2_reg32_set(&census_r, 0, TRIT2_FALSE);
    trit2_reg32_set(&census_r, 1, TRIT2_UNKNOWN);
    int nf = 0, nu = 0, nt = 0, nx = 0;
    trit2_reg32_census(census_r, &nf, &nu, &nt, &nx);
    CHECK("census: 1 false", nf == 1);
    CHECK("census: 1 unknown", nu == 1);
    CHECK("census: 30 true", nt == 30);
    CHECK("census: 0 faults", nx == 0);

    /* ==== 16. WCET Analysis ============================================ */
    printf("\n--- WCET Analysis ---\n");

    wcet_state_t wcet;
    wcet_init(&wcet);

    int w_alloc = wcet_register(&wcet, "mem_alloc",  WCET_MEM_ALLOC);
    int w_free  = wcet_register(&wcet, "mem_free",   WCET_MEM_FREE);
    int w_ipc   = wcet_register(&wcet, "ipc_send",   WCET_IPC_SEND);
    int w_dot   = wcet_register(&wcet, "dot_trit",   WCET_DOT_TRIT);
    int w_sched = wcet_register(&wcet, "sched_yield", WCET_SCHED_YIELD);
    CHECK("wcet: 5 probes registered", wcet.probe_count == 5);

    /* Simulate observations within budget */
    wcet_observe(&wcet, w_alloc, 150);
    wcet_observe(&wcet, w_alloc, 280);
    wcet_observe(&wcet, w_free,  500);
    wcet_observe(&wcet, w_ipc,   30);
    wcet_observe(&wcet, w_dot,   45);
    wcet_observe(&wcet, w_sched, 180);

    CHECK("wcet: no violations (within budget)", wcet_check(&wcet) == 0);
    CHECK("wcet: alloc max = 280", wcet.probes[w_alloc].observed_max == 280);
    CHECK("wcet: alloc util < 100%", wcet_utilization_pct(&wcet, w_alloc) < 100);
    CHECK("wcet: alloc avg > 0", wcet_average(&wcet, w_alloc) > 0);

    /* Simulate a violation */
    wcet_observe(&wcet, w_dot, 150);  /* exceeds 100-cycle budget */
    CHECK("wcet: 1 violation after overrun", wcet_check(&wcet) == 1);
    CHECK("wcet: dot utilization > 100%", wcet_utilization_pct(&wcet, w_dot) > 100);
    CHECK("wcet: global_tick accumulated", wcet.global_tick > 0);

    /* ==== QEMU Ternary Noise Simulation ================================ */
    printf("\n-- QEMU Noise Simulation --\n");

    /* Basic init */
    qemu_noise_t qn;
    qemu_noise_init(&qn, NOISE_NONE, 42, 1000);
    CHECK("qemu: init NONE model", qn.model == NOISE_NONE);

    /* NONE model = no noise */
    trit tn = TRIT_TRUE;
    trit noised = qemu_noise_read(&qn, tn);
    CHECK("qemu: NONE preserves TRUE", noised == TRIT_TRUE);
    noised = qemu_noise_read(&qn, TRIT_FALSE);
    CHECK("qemu: NONE preserves FALSE", noised == TRIT_FALSE);

    /* UNIFORM model */
    qemu_noise_init(&qn, NOISE_UNIFORM, 12345, 50000); /* 5% flip rate */
    int flipped = 0;
    for (int i = 0; i < 10000; i++) {
        trit r = qemu_noise_read(&qn, TRIT_TRUE);
        if (r != TRIT_TRUE) flipped++;
    }
    CHECK("qemu: UNIFORM flips some trits", flipped > 0);
    CHECK("qemu: UNIFORM flip rate < 20%", flipped < 2000);

    /* GAUSSIAN model */
    qemu_noise_init(&qn, NOISE_GAUSSIAN, 54321, 30000);
    flipped = 0;
    for (int i = 0; i < 10000; i++) {
        trit r = qemu_noise_read(&qn, TRIT_TRUE);
        if (r != TRIT_TRUE) flipped++;
    }
    CHECK("qemu: GAUSSIAN flips some trits", flipped > 0);
    CHECK("qemu: GAUSSIAN flip rate < 15%", flipped < 1500);

    /* MEMRISTIVE model */
    qemu_noise_init(&qn, NOISE_MEMRISTIVE, 99, 5000);
    flipped = 0;
    for (int i = 0; i < 10000; i++) {
        trit r = qemu_noise_read(&qn, TRIT_FALSE);
        if (r != TRIT_FALSE) flipped++;
    }
    CHECK("qemu: MEMRISTIVE flips some trits", flipped > 0);

    /* Register-level bulk noise */
    qemu_noise_init(&qn, NOISE_UNIFORM, 777, 100000); /* 10% rate */
    trit2_reg32 clean = trit2_reg32_splat(TRIT2_TRUE);
    int injected = qemu_noise_reg32(&qn, &clean);
    int diffs = 0;
    for (int i = 0; i < 32; i++) {
        if (trit2_reg32_get(&clean, i) != TRIT2_TRUE) diffs++;
    }
    CHECK("qemu: reg32 noise injects diffs", diffs > 0);
    CHECK("qemu: reg32 injected count matches", injected == diffs);

    /* Statistics tracking */
    CHECK("qemu: total_reads > 0", qn.total_reads > 0);
    CHECK("qemu: faults_injected > 0", qn.faults_injected > 0);
    double rate = (double)qn.faults_injected / qn.total_reads;
    CHECK("qemu: flip rate reasonable", rate > 0.001 && rate < 0.5);

    /* Reset stats */
    qemu_noise_reset_stats(&qn);
    CHECK("qemu: reset zeroes total_reads", qn.total_reads == 0);
    CHECK("qemu: reset zeroes faults", qn.faults_injected == 0);

    /* COSMIC model (rare bit-flip) */
    qemu_noise_init(&qn, NOISE_COSMIC, 42, 10000); /* 1% base, /10 = 0.1% */
    flipped = 0;
    for (int i = 0; i < 100000; i++) {
        trit r = qemu_noise_read(&qn, TRIT_UNKNOWN);
        if (r != TRIT_UNKNOWN) flipped++;
    }
    CHECK("qemu: COSMIC flips < 1%", flipped < 1000);

    /* ==== Summary ====================================================== */
    printf("\n========================================\n");
    printf("seT6 boot: %d tests, %d passed, %d failed\n",
           tests_run, tests_passed, tests_failed);
    printf("========================================\n");

    if (tests_failed == 0) {
        printf("seT6: ALL TESTS PASSED. Kernel operational.\n");
    } else {
        printf("seT6: %d FAILURES. See above.\n", tests_failed);
    }
}

/* ==== Entry Point ====================================================== */

int main(void) {
    set6_init();
    return 0;
}
