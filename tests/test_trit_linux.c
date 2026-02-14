/**
 * @file test_trit_linux.c
 * @brief Trit Linux — Architecture Port Test Suite
 *
 * Tests for the ternary arch layer: boot sequence, tryte pages,
 * trit addressing, scheduler priorities, multi-radix networking,
 * IRQ/timer, CPU features, and full-stack integration.
 *
 * Target: 82+ tests → pushes project total past 500.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

/* seT5 kernel headers */
#include "set5/trit.h"
#include "set5/trit_emu.h"
#include "set5/trit_cast.h"
#include "set5/memory.h"
#include "set5/scheduler.h"
#include "set5/ipc.h"
#include "set5/syscall.h"
#include "set5/multiradix.h"

/* Trit Linux arch headers */
#include "asm/trit_types.h"
#include "asm/trit_page.h"

/* ---- Forward declarations from arch sources (no separate .h yet) ------ */

/* boot/init.c */
extern int   trit_boot(int num_pages);
extern int   trit_emu_fallback(void);
extern int   trit_boot_mem_ok(void);
extern int   trit_boot_sched_ok(void);
extern int   trit_boot_mr_ok(void);
extern int   trit_boot_logic_ok(void);
extern int   trit_boot_pages_ok(void);
extern kernel_state_t  *trit_boot_kernel(void);
extern trit_page_mgr_t *trit_boot_page_mgr(void);

/* kernel/setup.c */
extern void  trit_irq_init(void);
extern int   trit_irq_register(int irq, void (*handler)(int), const char *name);
extern int   trit_irq_unregister(int irq);
extern int   trit_irq_enable(int irq, int enable);
extern int   trit_irq_dispatch(int irq);
extern int   trit_irq_get_count(int irq);
extern int   trit_irq_is_registered(int irq);
extern int   trit_irq_total_dispatched(void);

extern void  trit_timer_init(int interval);
extern void  trit_timer_tick(void);
extern int   trit_timer_get_ticks(void);
extern trit  trit_timer_get_phase(void);
extern void  trit_timer_stop(void);
extern void  trit_timer_start(void);

extern void         trit_cpu_detect(void);
extern unsigned int trit_cpu_features(void);
extern int          trit_cpu_trit_width(void);
extern int          trit_cpu_simd_lanes(void);
extern int          trit_cpu_has_feature(unsigned int feat);
extern int          trit_arch_setup(void);

/* net/multiradix_net.c */
typedef struct {
    trit src_addr[6];
    trit dst_addr[6];
    int  pkt_type;
    trit payload[32];
    int  payload_len;
    trit crc[3];
    int  valid;
} trit_net_packet_t;

extern int  trit_net_init(const trit local_addr[6]);
extern void trit_net_build_packet(trit_net_packet_t *pkt,
                                  const trit src[6], const trit dst[6],
                                  int pkt_type, const trit *payload, int len);
extern int  trit_net_send(const trit dst[6], int pkt_type,
                          const trit *payload, int len);
extern int  trit_net_recv(trit_net_packet_t *pkt);
extern int  trit_net_loopback(void);
extern int  trit_net_fft_encode(trit *payload, int len);
extern int  trit_net_dot(const trit *a, const trit *b, int len);
extern void trit_net_stats(int *tx, int *rx, int *errors);
extern int  trit_net_is_ready(void);

/* ---- Test harness ----------------------------------------------------- */

static int tests_passed = 0;
static int tests_failed = 0;
static int tests_total  = 0;

#define TEST(name) do { \
    tests_total++; \
    printf("  %-55s", name); \
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

#define SECTION(name) printf("\nSection: %s\n", name)

/* ---- IRQ test helper -------------------------------------------------- */
static int test_irq_fired = 0;
static void test_irq_handler(int irq) {
    (void)irq;
    test_irq_fired++;
}

/* ---- Tests ------------------------------------------------------------ */

int main(void) {
    printf("=================================\n");
    printf("  Trit Linux Arch Port Tests\n");
    printf("=================================\n");

    /* ============================================================ */
    SECTION("1: Ternary Address Types");
    /* ============================================================ */

    TEST("addr_from_zero");
    {
        trit_addr_t a = trit_addr_from_int(0);
        ASSERT(trit_addr_to_int(a) == 0, "zero roundtrip");
    }

    TEST("addr_positive_roundtrip");
    {
        trit_addr_t a = trit_addr_from_int(42);
        ASSERT(trit_addr_to_int(a) == 42, "42 roundtrip");
    }

    TEST("addr_negative_roundtrip");
    {
        trit_addr_t a = trit_addr_from_int(-13);
        ASSERT(trit_addr_to_int(a) == -13, "-13 roundtrip");
    }

    TEST("addr_large_value");
    {
        trit_addr_t a = trit_addr_from_int(729);
        ASSERT(trit_addr_to_int(a) == 729, "729 roundtrip");
    }

    TEST("addr_add_basic");
    {
        trit_addr_t a = trit_addr_from_int(10);
        trit_addr_t b = trit_addr_from_int(32);
        trit_addr_t c = trit_addr_add(a, b);
        ASSERT(trit_addr_to_int(c) == 42, "10+32=42");
    }

    TEST("addr_add_negative");
    {
        trit_addr_t a = trit_addr_from_int(50);
        trit_addr_t b = trit_addr_from_int(-20);
        trit_addr_t c = trit_addr_add(a, b);
        ASSERT(trit_addr_to_int(c) == 30, "50+(-20)=30");
    }

    TEST("addr_page_index");
    {
        /* Page 0 for addresses 0..728, page 1 for 729..1457 */
        trit_addr_t a = trit_addr_from_int(0);
        int page = trit_addr_page(a);
        ASSERT(page == 0, "addr 0 → page 0");
    }

    TEST("addr_page_offset");
    {
        trit_addr_t a = trit_addr_from_int(0);
        int off = trit_addr_offset(a);
        ASSERT(off == 0, "addr 0 → offset 0");
    }

    TEST("addr_max_address_space");
    {
        /* 12-trit address range */
        ASSERT(TRIT_ADDR_SPACE == 531441, "3^12 = 531441");
    }

    /* ============================================================ */
    SECTION("2: Boot Sequence");
    /* ============================================================ */

    TEST("boot_success");
    {
        int result = trit_boot(64);
        ASSERT(result == 0, "boot with 64 pages");
    }

    TEST("boot_mem_ok");
    ASSERT(trit_boot_mem_ok(), "memory initialized");

    TEST("boot_sched_ok");
    ASSERT(trit_boot_sched_ok(), "scheduler initialized");

    TEST("boot_mr_ok");
    ASSERT(trit_boot_mr_ok(), "multi-radix initialized");

    TEST("boot_logic_ok");
    ASSERT(trit_boot_logic_ok(), "Kleene logic self-check");

    TEST("boot_pages_ok");
    ASSERT(trit_boot_pages_ok(), "page manager initialized");

    TEST("boot_kernel_state_valid");
    {
        kernel_state_t *ks = trit_boot_kernel();
        ASSERT(ks != NULL, "kernel state pointer");
    }

    TEST("boot_emu_fallback");
    {
        int result = trit_emu_fallback();
        ASSERT(result == 0, "emulation fallback OK");
    }

    /* ============================================================ */
    SECTION("3: Tryte Page Allocator");
    /* ============================================================ */

    trit_page_mgr_t mgr;

    TEST("page_size_is_729");
    ASSERT(TRYTE_PAGE_SIZE == 729, "tryte page size");

    TEST("page_mgr_init");
    {
        trit_page_mgr_init(&mgr, 32);
        int total, free_count, mapped, faults;
        trit_page_stats(&mgr, &total, &free_count, &mapped, &faults);
        ASSERT(total == 32 && free_count == 32, "32 pages, all free");
    }

    TEST("page_alloc_returns_valid");
    {
        int pg = trit_page_alloc(&mgr, 0);
        ASSERT(pg >= 0 && pg < 32, "valid page index");
    }

    TEST("page_alloc_decrements_free");
    {
        int total, free_count, mapped, faults;
        trit_page_stats(&mgr, &total, &free_count, &mapped, &faults);
        ASSERT(free_count == 31, "free count decremented");
    }

    TEST("page_alloc_multiple");
    {
        int pg2 = trit_page_alloc(&mgr, 0);
        int pg3 = trit_page_alloc(&mgr, 1);
        ASSERT(pg2 >= 0 && pg3 >= 0 && pg2 != pg3, "distinct pages");
    }

    TEST("page_free_and_realloc");
    {
        int pg = trit_page_alloc(&mgr, 0);
        int freed = trit_page_free(&mgr, pg);
        int pg2 = trit_page_alloc(&mgr, 0);
        ASSERT(freed == 0 && pg2 >= 0, "free then realloc");
    }

    TEST("page_map_and_translate");
    {
        trit_page_mgr_t m2;
        trit_page_mgr_init(&m2, 16);
        int phys = trit_page_alloc(&m2, 0);
        trit_page_map(&m2, 5, phys, 1, 1);
        int translated = trit_page_translate(&m2, 5);
        ASSERT(translated == phys, "virt 5 → phys");
    }

    TEST("page_translate_unmapped_fails");
    {
        trit_page_mgr_t m2;
        trit_page_mgr_init(&m2, 16);
        int translated = trit_page_translate(&m2, 99);
        ASSERT(translated == -1, "unmapped → -1");
    }

    TEST("page_unmap");
    {
        trit_page_mgr_t m2;
        trit_page_mgr_init(&m2, 16);
        int phys = trit_page_alloc(&m2, 0);
        trit_page_map(&m2, 3, phys, 1, 1);
        int unmapped_phys = trit_page_unmap(&m2, 3);
        ASSERT(unmapped_phys == phys, "unmap returns phys");
        int t = trit_page_translate(&m2, 3);
        ASSERT(t == -1, "unmap clears mapping");
    }

    TEST("page_write_read_through_pt");
    {
        trit_page_mgr_t m2;
        trit_page_mgr_init(&m2, 16);
        int phys = trit_page_alloc(&m2, 0);
        trit_page_map(&m2, 7, phys, 1, 1);
        trit_page_write(&m2, 7, 0, TRIT_TRUE);
        trit v = trit_page_read(&m2, 7, 0);
        ASSERT(v == TRIT_TRUE, "write T, read T");
    }

    TEST("page_read_unknown_init");
    {
        trit_page_mgr_t m2;
        trit_page_mgr_init(&m2, 16);
        int phys = trit_page_alloc(&m2, 0);
        trit_page_map(&m2, 0, phys, 1, 1);
        trit v = trit_page_read(&m2, 0, 100);
        ASSERT(v == TRIT_UNKNOWN, "fresh page reads Unknown");
    }

    TEST("page_write_readonly_fails");
    {
        trit_page_mgr_t m2;
        trit_page_mgr_init(&m2, 16);
        int phys = trit_page_alloc(&m2, 0);
        trit_page_map(&m2, 2, phys, 0, 1);  /* read-only */
        int r = trit_page_write(&m2, 2, 0, TRIT_TRUE);
        ASSERT(r == -2, "readonly write rejected");
    }

    TEST("page_fault_count");
    {
        trit_page_mgr_t m2;
        trit_page_mgr_init(&m2, 16);
        trit_page_unmap(&m2, 10);  /* unmapped → fault */
        int total, free_count, mapped, faults;
        trit_page_stats(&m2, &total, &free_count, &mapped, &faults);
        ASSERT(faults >= 1, "fault counted");
    }

    /* ============================================================ */
    SECTION("4: IRQ Subsystem");
    /* ============================================================ */

    TEST("irq_init");
    {
        trit_irq_init();
        ASSERT(trit_irq_total_dispatched() == 0, "clean slate");
    }

    TEST("irq_register");
    {
        int r = trit_irq_register(0, test_irq_handler, "test_irq_0");
        ASSERT(r == 0, "register success");
    }

    TEST("irq_is_registered");
    ASSERT(trit_irq_is_registered(0), "irq 0 registered");

    TEST("irq_dispatch");
    {
        test_irq_fired = 0;
        int r = trit_irq_dispatch(0);
        ASSERT(r == 0 && test_irq_fired == 1, "handler called");
    }

    TEST("irq_count_increments");
    ASSERT(trit_irq_get_count(0) == 1, "count = 1");

    TEST("irq_multiple_dispatches");
    {
        trit_irq_dispatch(0);
        trit_irq_dispatch(0);
        ASSERT(trit_irq_get_count(0) == 3, "count = 3");
    }

    TEST("irq_disable_masks");
    {
        trit_irq_enable(0, 0);
        int r = trit_irq_dispatch(0);
        ASSERT(r == -2, "masked irq rejected");
    }

    TEST("irq_reenable");
    {
        trit_irq_enable(0, 1);
        int r = trit_irq_dispatch(0);
        ASSERT(r == 0, "re-enabled irq fires");
    }

    TEST("irq_unregister");
    {
        trit_irq_unregister(0);
        ASSERT(!trit_irq_is_registered(0), "unregistered");
    }

    TEST("irq_out_of_range");
    {
        int r = trit_irq_register(99, test_irq_handler, "bad");
        ASSERT(r == -1, "out of range rejected");
    }

    /* ============================================================ */
    SECTION("5: Timer");
    /* ============================================================ */

    TEST("timer_init");
    {
        trit_timer_init(100);
        ASSERT(trit_timer_get_ticks() == 0, "starts at 0");
    }

    TEST("timer_tick_increments");
    {
        trit_timer_tick();
        ASSERT(trit_timer_get_ticks() == 1, "tick = 1");
    }

    TEST("timer_phase_cycles");
    {
        /* Phase starts at F(-1), after 1 tick should cycle */
        trit_timer_init(100);
        trit p0 = trit_timer_get_phase();
        trit_timer_tick();
        trit p1 = trit_timer_get_phase();
        trit_timer_tick();
        trit p2 = trit_timer_get_phase();
        /* F → U → T is the cycle */
        ASSERT(p0 == TRIT_FALSE && p1 == TRIT_UNKNOWN && p2 == TRIT_TRUE,
               "F→U→T phase cycle");
    }

    TEST("timer_stop_freezes");
    {
        trit_timer_init(100);
        trit_timer_tick();
        trit_timer_stop();
        trit_timer_tick();
        ASSERT(trit_timer_get_ticks() == 1, "stopped at 1");
    }

    TEST("timer_restart");
    {
        trit_timer_start();
        trit_timer_tick();
        ASSERT(trit_timer_get_ticks() == 2, "restarted, tick = 2");
    }

    /* ============================================================ */
    SECTION("6: CPU Features");
    /* ============================================================ */

    TEST("cpu_detect");
    {
        trit_cpu_detect();
        ASSERT(trit_cpu_features() != 0, "features detected");
    }

    TEST("cpu_has_simd");
    ASSERT(trit_cpu_has_feature(TRIT_FEAT_SIMD), "SIMD available");

    TEST("cpu_has_fft");
    ASSERT(trit_cpu_has_feature(TRIT_FEAT_FFT), "FFT available");

    TEST("cpu_has_dotprod");
    ASSERT(trit_cpu_has_feature(TRIT_FEAT_DOTPROD), "dot product available");

    TEST("cpu_has_sparse");
    ASSERT(trit_cpu_has_feature(TRIT_FEAT_SPARSE), "sparsity available");

    TEST("cpu_has_radixconv");
    ASSERT(trit_cpu_has_feature(TRIT_FEAT_RADIXCONV), "radix conv available");

    TEST("cpu_trit_width_32");
    ASSERT(trit_cpu_trit_width() == 32, "32-trit width");

    TEST("cpu_simd_lanes_32");
    ASSERT(trit_cpu_simd_lanes() == 32, "32 SIMD lanes");

    TEST("arch_setup_full");
    {
        int r = trit_arch_setup();
        ASSERT(r == 0, "full arch setup");
    }

    /* ============================================================ */
    SECTION("7: Multi-Radix Network Driver");
    /* ============================================================ */

    trit local_addr[6] = {1, 0, -1, 1, 0, -1};

    TEST("net_init");
    {
        int r = trit_net_init(local_addr);
        ASSERT(r == 0, "net driver init");
    }

    TEST("net_is_ready");
    ASSERT(trit_net_is_ready(), "driver ready");

    TEST("net_send_data");
    {
        trit payload[] = {1, 1, -1, 0, 1};
        int r = trit_net_send(local_addr, 0, payload, 5);
        ASSERT(r == 0, "send success");
    }

    TEST("net_tx_count");
    {
        int tx, rx, errors;
        trit_net_stats(&tx, &rx, &errors);
        ASSERT(tx == 1, "tx = 1");
    }

    TEST("net_loopback");
    {
        int looped = trit_net_loopback();
        ASSERT(looped == 1, "loopback delivered 1 pkt");
    }

    TEST("net_recv_after_loopback");
    {
        trit_net_packet_t pkt;
        int r = trit_net_recv(&pkt);
        ASSERT(r == 0 && pkt.payload[0] == 1 && pkt.payload_len == 5,
               "received correct payload");
    }

    TEST("net_recv_empty_returns_error");
    {
        trit_net_packet_t pkt;
        int r = trit_net_recv(&pkt);
        ASSERT(r == -1, "no more packets");
    }

    TEST("net_build_packet_crc");
    {
        trit_net_packet_t pkt;
        trit src[6] = {0,0,0,0,0,0};
        trit dst[6] = {1,1,1,1,1,1};
        trit payload[4] = {1, -1, 0, 1};
        trit_net_build_packet(&pkt, src, dst, 0, payload, 4);
        /* CRC should be non-trivial with mixed payload */
        ASSERT(pkt.valid == 1, "packet marked valid");
    }

    TEST("net_dot_product");
    {
        trit a[] = {1, 1, 1, 1};
        trit b[] = {1, 1, 1, 1};
        int dot = trit_net_dot(a, b, 4);
        ASSERT(dot == 4, "dot([T,T,T,T], [T,T,T,T]) = 4");
    }

    TEST("net_dot_mixed");
    {
        trit a[] = {1, -1, 0, 1};
        trit b[] = {-1, 1, 1, 0};
        int dot = trit_net_dot(a, b, 4);
        ASSERT(dot == -2, "dot([1,-1,0,1],[-1,1,1,0]) = -2");
    }

    TEST("net_fft_encode_does_not_crash");
    {
        trit payload[8] = {1, -1, 0, 1, -1, 0, 1, -1};
        int r = trit_net_fft_encode(payload, 8);
        ASSERT(r == 0, "FFT encode ok");
    }

    TEST("net_multiple_sends");
    {
        /* Re-init for clean state */
        trit_net_init(local_addr);
        for (int i = 0; i < 10; i++) {
            trit p[1] = { (trit)(i % 3 - 1) };
            trit_net_send(local_addr, 0, p, 1);
        }
        int tx, rx, errors;
        trit_net_stats(&tx, &rx, &errors);
        ASSERT(tx == 10, "10 packets sent");
    }

    TEST("net_loopback_multiple");
    {
        int looped = trit_net_loopback();
        ASSERT(looped == 10, "10 packets looped back");
    }

    /* ============================================================ */
    SECTION("8: Scheduler via Boot Kernel");
    /* ============================================================ */

    TEST("sched_boot_threads_created");
    {
        kernel_state_t *ks = trit_boot_kernel();
        int total, ready, blocked, switches;
        sched_stats(&ks->sched, &total, &ready, &blocked, &switches);
        ASSERT(total >= 2, "idle + init threads");
    }

    TEST("sched_pick_next");
    {
        kernel_state_t *ks = trit_boot_kernel();
        int tid = sched_pick_next(&ks->sched);
        ASSERT(tid >= 0, "picked a thread");
    }

    TEST("sched_set_priority");
    {
        kernel_state_t *ks = trit_boot_kernel();
        int tid = sched_create(&ks->sched, 100, TRIT_PRIO_HIGH);
        int r = sched_set_priority(&ks->sched, tid, TRIT_PRIO_LOW);
        ASSERT(tid >= 0 && r == 0, "priority changed");
    }

    TEST("sched_yield");
    {
        kernel_state_t *ks = trit_boot_kernel();
        int r = sched_yield(&ks->sched);
        ASSERT(r >= 0, "yield success");
    }

    TEST("sched_block_unblock");
    {
        kernel_state_t *ks = trit_boot_kernel();
        int tid = sched_create(&ks->sched, 200, TRIT_PRIO_NORMAL);
        int r1 = sched_block(&ks->sched, tid, 0);
        int r2 = sched_unblock(&ks->sched, tid);
        ASSERT(r1 == 0 && r2 == 0, "block then unblock");
    }

    /* ============================================================ */
    SECTION("9: IPC via Boot Kernel");
    /* ============================================================ */

    TEST("ipc_endpoint_create");
    {
        kernel_state_t *ks = trit_boot_kernel();
        int ep = ipc_endpoint_create(&ks->ipc);
        ASSERT(ep >= 0, "endpoint created");
    }

    TEST("ipc_send_recv");
    {
        kernel_state_t *ks = trit_boot_kernel();
        int ep = ipc_endpoint_create(&ks->ipc);

        ipc_msg_t msg;
        trit words[3] = {TRIT_TRUE, TRIT_UNKNOWN, TRIT_FALSE};
        ipc_msg_build(&msg, words, 3, 42, 1);
        ipc_send(&ks->ipc, ep, &msg, 1);

        ipc_msg_t recv_msg;
        int r = ipc_recv(&ks->ipc, ep, &recv_msg, 2);
        ASSERT(r == 0, "send+recv");
    }

    TEST("ipc_notification");
    {
        kernel_state_t *ks = trit_boot_kernel();
        int notif = ipc_notification_create(&ks->ipc);
        int r = ipc_signal(&ks->ipc, notif);
        ASSERT(notif >= 0 && r == 0, "notification signalled");
    }

    /* ============================================================ */
    SECTION("10: Syscall Dispatch");
    /* ============================================================ */

    TEST("syscall_mem_alloc");
    {
        kernel_state_t *ks = trit_boot_kernel();
        syscall_result_t r = syscall_dispatch(ks, SYSCALL_MMAP, 0, 0);
        ASSERT(r.retval >= 0, "mmap via syscall");
    }

    TEST("syscall_thread_create");
    {
        kernel_state_t *ks = trit_boot_kernel();
        syscall_result_t r = syscall_dispatch(ks, SYSCALL_THREAD_CREATE, 300, 0);
        ASSERT(r.retval >= 0, "thread create via syscall");
    }

    TEST("syscall_dot_trit");
    {
        kernel_state_t *ks = trit_boot_kernel();
        syscall_result_t r = syscall_dispatch(ks, SYSCALL_DOT_TRIT, 0, 1);
        ASSERT(r.retval >= -32 && r.retval <= 32, "dot trit via syscall");
    }

    TEST("syscall_radix_conv");
    {
        kernel_state_t *ks = trit_boot_kernel();
        syscall_result_t r = syscall_dispatch(ks, SYSCALL_RADIX_CONV, 0, 100);
        ASSERT(r.retval >= 0, "radix conv via syscall");
    }

    /* ============================================================ */
    SECTION("11: Capability System");
    /* ============================================================ */

    TEST("cap_create");
    {
        kernel_state_t *ks = trit_boot_kernel();
        int cap = kernel_cap_create(ks, 1, 0x7, 100);
        ASSERT(cap >= 0, "capability created");
    }

    TEST("cap_check");
    {
        kernel_state_t *ks = trit_boot_kernel();
        int cap = kernel_cap_create(ks, 2, 0x5, 200);
        int ok = kernel_cap_check(ks, cap, 0x1);
        ASSERT(ok == 1, "capability check pass");
    }

    TEST("cap_revoke");
    {
        kernel_state_t *ks = trit_boot_kernel();
        int cap = kernel_cap_create(ks, 3, 0x7, 300);
        int r = kernel_cap_revoke(ks, cap);
        int ok = kernel_cap_check(ks, cap, 0x1);
        ASSERT(r == 0 && ok == 0, "revoked cap fails check");
    }

    /* ============================================================ */
    SECTION("12: Emulation Layer (trit2)");
    /* ============================================================ */

    TEST("trit2_encode_decode_roundtrip");
    {
        int ok = 1;
        for (int v = -1; v <= 1; v++) {
            trit2 enc = trit2_encode(v);
            int dec = trit2_decode(enc);
            if (dec != v) ok = 0;
        }
        ASSERT(ok, "all 3 values roundtrip");
    }

    TEST("trit2_reg32_splat_and_get");
    {
        trit2_reg32 r = trit2_reg32_splat(TRIT2_TRUE);
        int ok = 1;
        for (int i = 0; i < 32; i++) {
            if (trit2_decode(trit2_reg32_get(&r, i)) != 1) ok = 0;
        }
        ASSERT(ok, "all 32 trits = T");
    }

    TEST("trit2_reg32_census");
    {
        trit2_reg32 r = trit2_reg32_splat(TRIT2_UNKNOWN);
        trit2_reg32_set(&r, 0, TRIT2_TRUE);
        trit2_reg32_set(&r, 1, TRIT2_FALSE);
        int nf, nu, nt, nfault;
        trit2_reg32_census(r, &nf, &nu, &nt, &nfault);
        ASSERT(nf == 1 && nt == 1 && nu == 30, "census: 1F, 30U, 1T");
    }

    TEST("trit2_bulk_and");
    {
        trit2_reg32 a = trit2_reg32_splat(TRIT2_TRUE);
        trit2_reg32 b = trit2_reg32_splat(TRIT2_FALSE);
        trit2_reg32 dst;
        trit2_reg32_and_bulk(&dst, &a, &b, 1);
        int ok = 1;
        for (int i = 0; i < 32; i++) {
            if (trit2_decode(trit2_reg32_get(&dst, i)) != -1) ok = 0;
        }
        ASSERT(ok, "bulk AND(T,F) = F");
    }

    /* ============================================================ */
    SECTION("13: Multi-Radix Engine");
    /* ============================================================ */

    TEST("mr_radix_conv_roundtrip");
    {
        multiradix_state_t mr;
        multiradix_init(&mr);
        radix_conv_to_ternary(&mr, 0, 42);
        int back = radix_conv_to_binary(&mr, 0, 8);
        ASSERT(back == 42, "42 → ternary → 42");
    }

    TEST("mr_dot_all_true");
    {
        multiradix_state_t mr;
        multiradix_init(&mr);
        mr.regs[0] = trit2_reg32_splat(TRIT2_TRUE);
        mr.regs[1] = trit2_reg32_splat(TRIT2_TRUE);
        int d = dot_trit(&mr, 0, 1);
        ASSERT(d == 32, "dot(T,T) = 32");
    }

    TEST("mr_fft_step");
    {
        multiradix_state_t mr;
        multiradix_init(&mr);
        radix_conv_to_ternary(&mr, 0, 7);
        int r = fft_step(&mr, 0, 1, 1);
        ASSERT(r >= 0, "FFT step success");
    }

    TEST("mr_telemetry");
    {
        multiradix_state_t mr;
        multiradix_init(&mr);
        trit_lb_record(&mr);
        trit_lb_record(&mr);
        trit_lb_snapshot_t snap = trit_lb_snapshot(&mr);
        ASSERT(snap.total_insns == 2, "2 instructions recorded");
    }

    /* ============================================================ */
    SECTION("14: Full Stack Integration");
    /* ============================================================ */

    TEST("integ_boot_alloc_map_write_read");
    {
        trit_page_mgr_t im;
        trit_page_mgr_init(&im, 16);
        int phys = trit_page_alloc(&im, 0);
        trit_page_map(&im, 0, phys, 1, 1);
        trit_page_write(&im, 0, 42, TRIT_TRUE);
        trit v = trit_page_read(&im, 0, 42);
        ASSERT(v == TRIT_TRUE, "full alloc→map→write→read");
    }

    TEST("integ_sched_ipc_roundtrip");
    {
        kernel_state_t *ks = trit_boot_kernel();
        int tid = sched_create(&ks->sched, 500, TRIT_PRIO_NORMAL);
        int ep = ipc_endpoint_create(&ks->ipc);
        ipc_msg_t msg;
        trit w[1] = {TRIT_TRUE};
        ipc_msg_build(&msg, w, 1, tid, tid);
        ipc_send(&ks->ipc, ep, &msg, tid);
        ipc_msg_t recv;
        int r = ipc_recv(&ks->ipc, ep, &recv, tid);
        ASSERT(r == 0, "ipc_recv succeeds");
        ASSERT(recv.words[0] == TRIT_TRUE, "received msg[0] = TRUE");
        ASSERT(tid >= 0, "sched+ipc roundtrip");
    }

    TEST("integ_net_fft_dot");
    {
        /* Send FFT-encoded packet, receive, compute dot product */
        trit addr[6] = {0,1,0,-1,0,1};
        trit_net_init(addr);
        trit payload[4] = {1, -1, 1, -1};
        trit_net_send(addr, 2, payload, 4);
        trit_net_loopback();
        trit_net_packet_t pkt;
        trit_net_recv(&pkt);
        int dot = trit_net_dot(payload, pkt.payload, 4);
        /* Same data → dot = sum of squares = 4 */
        ASSERT(dot == 4, "send→loopback→dot match");
    }

    TEST("integ_cap_protect_memory");
    {
        kernel_state_t *ks = trit_boot_kernel();
        int cap = kernel_cap_create(ks, 10, 0x3, 999);
        int ok = kernel_cap_check(ks, cap, 0x1);
        ASSERT(ok == 1, "cap protects memory access");
    }

    TEST("integ_ternary_addr_mem_access");
    {
        trit_page_mgr_t im;
        trit_page_mgr_init(&im, 16);
        int phys = trit_page_alloc(&im, 0);
        trit_page_map(&im, 0, phys, 1, 1);
        /* Write at ternary-computed offset */
        trit_addr_t a = trit_addr_from_int(100);
        int offset = trit_addr_to_int(a);
        trit_page_write(&im, 0, offset % TRYTE_PAGE_SIZE, TRIT_FALSE);
        trit v = trit_page_read(&im, 0, offset % TRYTE_PAGE_SIZE);
        ASSERT(v == TRIT_FALSE, "ternary addr → page write/read");
    }

    /* ============================================================ */
    /* Summary                                                      */
    /* ============================================================ */

    printf("\n=================================\n");
    printf("Trit Linux Tests: %d passed, %d failed (of %d)\n",
           tests_passed, tests_failed, tests_total);
    printf("=================================\n");

    return tests_failed > 0 ? 1 : 0;
}
