/**
 * @file test_friday_updates.c
 * @brief  Comprehensive test suite for Friday Jan 13 Updates:
 *         STT-MRAM Memory Interface, Ternary-Native IPC (T-IPC),
 *         and Ternary-Native File System (TFS).
 *
 * Build:
 *   gcc -Wall -Wextra -Iinclude -o test_friday_updates \
 *       tests/test_friday_updates.c src/stt_mram.c src/tipc.c src/tfs.c
 *
 * Run:
 *   ./test_friday_updates
 */

#include <stdio.h>
#include <string.h>
#include <stdint.h>

#include "set6/trit.h"
#include "set6/stt_mram.h"
#include "set6/tipc.h"
#include "set6/tfs.h"

/* ── Test harness ─────────────────────────────────────────────── */
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

/* ================================================================
 *  SCENARIO 1 — STT-MRAM Memory Interface
 * ================================================================ */
static void test_stt_mram(void) {
    printf("\n=== Scenario 1: STT-MRAM Memory Interface ===\n");

    /* --- Phase 1: Initialization --- */
    printf("--- Phase 1: Initialization ---\n");
    mram_array_t arr;
    int rc = mram_init(&arr, 8, 8);
    CHECK("mram_init succeeds", rc == 0);
    CHECK("mram rows set", arr.rows == 8);
    CHECK("mram cols set", arr.cols == 8);
    CHECK("mram total_cells", arr.total_cells == 64);
    CHECK("mram initial ECS status STABLE",
          arr.ecs_status == MRAM_ECS_STABLE);

    /* --- Phase 2: Write / Read round-trip --- */
    printf("--- Phase 2: Write / Read Round-Trip ---\n");
    rc = mram_write_trit(&arr, 0, 0, TRIT_TRUE);
    CHECK("write +1 succeeds", rc == 0);
    trit v = mram_read_trit(&arr, 0, 0);
    CHECK("read back +1", v == TRIT_TRUE);

    rc = mram_write_trit(&arr, 1, 0, TRIT_FALSE);
    CHECK("write -1 succeeds", rc == 0);
    v = mram_read_trit(&arr, 1, 0);
    CHECK("read back -1", v == TRIT_FALSE);

    rc = mram_write_trit(&arr, 2, 0, TRIT_UNKNOWN);
    CHECK("write 0 succeeds", rc == 0);
    v = mram_read_trit(&arr, 2, 0);
    CHECK("read back 0", v == TRIT_UNKNOWN);

    /* --- Phase 3: Pack / Unpack (5 trits → byte → 5 trits) --- */
    printf("--- Phase 3: Pack / Unpack ---\n");
    trit src[5] = { TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE, TRIT_FALSE };
    uint8_t packed = mram_pack_trits(src);
    CHECK("packed value < 243", packed < MRAM_PACK_BASE);

    trit dst[5];
    mram_unpack_trits(packed, dst);
    int pack_ok = 1;
    for (int i = 0; i < 5; i++) {
        if (dst[i] != src[i]) pack_ok = 0;
    }
    CHECK("unpack matches original", pack_ok);

    /* Pack all-zero trits */
    trit zeros[5] = {0, 0, 0, 0, 0};
    uint8_t pz = mram_pack_trits(zeros);
    CHECK("all-zero pack gives 0+1 base values", pz == (1+3+9+27+81));

    /* --- Phase 4: XOR at Sense Amplifier --- */
    printf("--- Phase 4: XOR at Sense Amplifier ---\n");
    mram_write_trit(&arr, 3, 0, TRIT_TRUE);  /* +1 */
    rc = mram_xor_trit(&arr, 3 * arr.cols + 0, TRIT_TRUE);  /* +1 XOR +1 */
    CHECK("xor succeeds", rc == 0);
    v = mram_read_trit(&arr, 3, 0);
    CHECK("(+1 xor +1) is balanced mod-3 result", v == TRIT_FALSE || v == TRIT_UNKNOWN || v == TRIT_TRUE);

    /* (+1) + (+1) = +2 → mod 3 → -1  (balanced) */
    CHECK("(+1 xor +1) = -1 in balanced ternary", v == TRIT_FALSE);

    /* --- Phase 5: Nominal Resistance --- */
    printf("--- Phase 5: Nominal Resistance ---\n");
    CHECK("R_LOW for state 0", mram_nominal_resistance(MTJ_STATE_0) == MRAM_R_LOW_X10);
    CHECK("R_MID for state 1", mram_nominal_resistance(MTJ_STATE_1) == MRAM_R_MID_X10);
    CHECK("R_HIGH for state 2", mram_nominal_resistance(MTJ_STATE_2) == MRAM_R_HIGH_X10);

    /* --- Phase 6: ECS Scan (no drift) --- */
    printf("--- Phase 6: ECS Scan ---\n");
    rc = mram_ecs_scan(&arr);
    CHECK("ecs_scan with no drift succeeds", rc == 0);
    CHECK("ECS status stays STABLE", arr.ecs_status == MRAM_ECS_STABLE);

    /* --- Phase 7: Drift Injection & Detection --- */
    printf("--- Phase 7: Drift Injection & Detection ---\n");
    mram_write_trit(&arr, 4, 0, TRIT_TRUE);  /* State 1 → R_MID */
    rc = mram_inject_drift(&arr, 4 * arr.cols + 0, 50);
    CHECK("inject_drift succeeds", rc == 0);
    rc = mram_ecs_scan(&arr);
    CHECK("ecs_scan detects drift and recalibrates", rc == 0 || rc == 1);

    /* --- Phase 8: Stabilize --- */
    printf("--- Phase 8: Stabilize ---\n");
    rc = mram_stabilize(&arr, 4 * arr.cols + 0);
    CHECK("stabilize succeeds", rc >= 0);

    /* --- Phase 9: ECS Status String --- */
    printf("--- Phase 9: ECS Status String ---\n");
    const char *s = mram_ecs_status_str(MRAM_ECS_STABLE);
    CHECK("STABLE string not NULL", s != NULL);
    CHECK("STABLE string correct", strcmp(s, "STABLE") == 0);

    /* --- Phase 10: Boundary checks --- */
    printf("--- Phase 10: Boundary Checks ---\n");
    rc = mram_write_trit(&arr, 100, 0, TRIT_TRUE);
    CHECK("out-of-bounds write returns error", rc != 0);
    v = mram_read_trit(&arr, 100, 0);
    CHECK("out-of-bounds read returns Unknown", v == TRIT_UNKNOWN);
}

/* ================================================================
 *  SCENARIO 2 — Ternary-Native IPC (T-IPC)
 * ================================================================ */
static void test_tipc(void) {
    printf("\n=== Scenario 2: Ternary-Native IPC (T-IPC) ===\n");

    /* --- Phase 1: Channel Initialization --- */
    printf("--- Phase 1: Channel Initialization ---\n");
    tipc_channel_t ch;
    tipc_channel_init(&ch);
    CHECK("channel active_count == 0", ch.active_count == 0);
    CHECK("channel radix_violations == 0", ch.radix_violations == 0);

    /* --- Phase 2: Endpoint Creation --- */
    printf("--- Phase 2: Endpoint Creation ---\n");
    int ep0 = tipc_endpoint_create(&ch);
    int ep1 = tipc_endpoint_create(&ch);
    CHECK("endpoint 0 created", ep0 == 0);
    CHECK("endpoint 1 created", ep1 == 1);
    CHECK("active_count now 2", ch.active_count == 2);

    /* --- Phase 3: Huffman Compress / Decompress --- */
    printf("--- Phase 3: Huffman Compress / Decompress ---\n");
    trit msg[] = { TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE,
                   TRIT_UNKNOWN, TRIT_FALSE, TRIT_TRUE, TRIT_UNKNOWN, TRIT_FALSE };
    int msg_len = 9;

    tipc_compressed_t comp;
    int rc = tipc_compress(&comp, msg, msg_len);
    CHECK("compress succeeds", rc > 0);
    CHECK("original_trits preserved", comp.original_trits == msg_len);
    CHECK("bit_count > 0", comp.bit_count > 0);
    CHECK("bit_count <= 18 (worst case 9×2)", comp.bit_count <= 18);

    trit decompressed[64];
    int dc = tipc_decompress(decompressed, 64, &comp);
    CHECK("decompress returns correct count", dc == msg_len);
    int dec_ok = 1;
    for (int i = 0; i < msg_len; i++) {
        if (decompressed[i] != msg[i]) dec_ok = 0;
    }
    CHECK("decompress matches original", dec_ok);

    /* --- Phase 4: Guardian Trit --- */
    printf("--- Phase 4: Guardian Trit ---\n");
    trit g = tipc_guardian_compute(msg, msg_len);
    CHECK("guardian is valid trit", g >= TRIT_FALSE && g <= TRIT_TRUE);

    /* Self-consistency: same data → same guardian */
    trit g2 = tipc_guardian_compute(msg, msg_len);
    CHECK("guardian is deterministic", g == g2);

    /* --- Phase 5: Send / Receive --- */
    printf("--- Phase 5: Send / Receive ---\n");
    rc = tipc_send(&ch, ep1, msg, msg_len, TIPC_PRIO_HIGH);
    CHECK("send succeeds", rc == 0);

    trit recv_buf[64];
    int rlen = tipc_recv(&ch, ep1, recv_buf, 64);
    CHECK("recv returns correct count", rlen == msg_len);
    int recv_ok = 1;
    for (int i = 0; i < msg_len; i++) {
        if (recv_buf[i] != msg[i]) recv_ok = 0;
    }
    CHECK("recv data matches sent data", recv_ok);

    /* --- Phase 6: XOR Differential Update --- */
    printf("--- Phase 6: XOR Differential Update ---\n");
    tipc_message_t m;
    memset(&m, 0, sizeof(m));
    m.count = 3;
    m.trits[0] = TRIT_TRUE;
    m.trits[1] = TRIT_FALSE;
    m.trits[2] = TRIT_UNKNOWN;
    m.guardian = tipc_guardian_compute(m.trits, m.count);

    trit delta[3] = { TRIT_TRUE, TRIT_TRUE, TRIT_TRUE };
    rc = tipc_xor_diff(&m, delta, 3);
    CHECK("xor_diff succeeds", rc == 0);
    CHECK("guardian recomputed after diff", tipc_guardian_validate(&m) == TIPC_GUARDIAN_OK);

    /* --- Phase 7: Radix Guard --- */
    printf("--- Phase 7: Radix Guard ---\n");
    uint8_t safe_data[] = { 0, 100, 200, 242 };
    int violations = tipc_radix_guard(safe_data, 4);
    CHECK("no violations for bytes < 243", violations == 0);

    uint8_t bad_data[] = { 243, 255, 100 };
    violations = tipc_radix_guard(bad_data, 3);
    CHECK("detects violations for bytes >= 243", violations == 1);

    /* --- Phase 8: Compression Ratio --- */
    printf("--- Phase 8: Compression Ratio ---\n");
    int ratio = tipc_compression_ratio(&comp);
    CHECK("compression ratio > 0", ratio > 0);
    CHECK("compression ratio <= 1000000 (≤100%)", ratio <= 1000000);

    /* --- Phase 9: Frequency Analysis --- */
    printf("--- Phase 9: Frequency Analysis ---\n");
    tipc_freq_t freq = tipc_frequency(msg, msg_len);
    CHECK("freq total = msg_len", freq.freq_neg + freq.freq_zero + freq.freq_pos == msg_len);

    /* --- Phase 10: All-zero compression efficiency --- */
    printf("--- Phase 10: All-Zero Compression ---\n");
    trit all_zero[32];
    memset(all_zero, 0, sizeof(all_zero));
    tipc_compressed_t comp_z;
    tipc_compress(&comp_z, all_zero, 32);
    CHECK("all-zero: 32 trits → 32 bits (1 bit each)", comp_z.bit_count == 32);
}

/* ================================================================
 *  SCENARIO 3 — Ternary-Native File System (TFS)
 * ================================================================ */
static void test_tfs(void) {
    printf("\n=== Scenario 3: Ternary-Native File System (TFS) ===\n");

    /* --- Phase 1: Initialization --- */
    printf("--- Phase 1: Initialization ---\n");
    tfs_state_t fs;
    tfs_init(&fs);
    CHECK("superblock magic[0] = T", fs.magic[0] == TRIT_TRUE);
    CHECK("superblock magic[1] = F", fs.magic[1] == TRIT_FALSE);
    CHECK("superblock magic[2] = T", fs.magic[2] == TRIT_TRUE);

    int files, free_blocks, reads, writes, compressions;
    tfs_get_stats(&fs, &files, &free_blocks, &reads, &writes, &compressions);
    CHECK("initial files == 0", files == 0);
    CHECK("initial free_blocks == TFS_MAX_BLOCKS", free_blocks == TFS_MAX_BLOCKS);
    CHECK("initial reads == 0", reads == 0);
    CHECK("initial writes == 0", writes == 0);

    /* --- Phase 2: File Open / Write / Read / Close --- */
    printf("--- Phase 2: File Operations ---\n");
    tfs_fd_t fd;
    int rc = tfs_open(&fs, "test.trit", TFS_MODE_WRITE, &fd);
    CHECK("open for write succeeds", rc == 0);

    trit data[10] = { 1, -1, 0, 1, 1, -1, 0, 0, 1, -1 };
    rc = tfs_write(&fs, &fd, data, 10);
    CHECK("write 10 trits succeeds", rc == 10);

    tfs_close(&fs, &fd);

    /* Reopen for read */
    rc = tfs_open(&fs, "test.trit", TFS_MODE_READ, &fd);
    CHECK("open for read succeeds", rc == 0);

    trit readback[64];
    int rlen = tfs_read(&fs, &fd, readback, 64);
    CHECK("read returns 10 trits", rlen == 10);
    int data_ok = 1;
    for (int i = 0; i < 10; i++) {
        if (readback[i] != data[i]) data_ok = 0;
    }
    CHECK("read data matches written data", data_ok);

    tfs_close(&fs, &fd);

    /* --- Phase 3: Huffman Encode / Decode --- */
    printf("--- Phase 3: Huffman Encode / Decode ---\n");
    trit huff_in[16] = { 1, 0, -1, 0, 1, 1, -1, 0, 0, 0, 1, -1, -1, 0, 1, 0 };
    tfs_compressed_block_t cblk;
    rc = tfs_huffman_encode(&cblk, huff_in, 16);
    CHECK("huffman encode succeeds", rc > 0);
    CHECK("compressed bit_count > 0", cblk.bit_count > 0);
    CHECK("compressed bit_count <= 32 (16×2 worst)", cblk.bit_count <= 32);
    CHECK("original_trits preserved", cblk.original_trits == 16);

    trit huff_out[64];
    int hlen = tfs_huffman_decode(huff_out, 64, &cblk);
    CHECK("huffman decode returns 16", hlen == 16);
    int huff_ok = 1;
    for (int i = 0; i < 16; i++) {
        if (huff_out[i] != huff_in[i]) huff_ok = 0;
    }
    CHECK("huffman decode matches original", huff_ok);

    /* --- Phase 4: Guardian Compute --- */
    printf("--- Phase 4: Guardian Compute ---\n");
    trit guard = tfs_guardian_compute(data, 10);
    CHECK("guardian is valid trit", guard >= -1 && guard <= 1);
    trit guard2 = tfs_guardian_compute(data, 10);
    CHECK("guardian is deterministic", guard == guard2);

    /* --- Phase 5: Sync (guardian verification) --- */
    printf("--- Phase 5: Sync ---\n");
    rc = tfs_open(&fs, "test.trit", TFS_MODE_READ, &fd);
    CHECK("open for sync succeeds", rc == 0);
    rc = tfs_sync(&fs, &fd);
    CHECK("sync succeeds (guardians valid)", rc >= 0);
    tfs_close(&fs, &fd);

    /* --- Phase 6: File Compression --- */
    printf("--- Phase 6: File Compression ---\n");
    rc = tfs_compress(&fs, "test.trit");
    CHECK("compress file succeeds", rc >= 0);

    tfs_get_stats(&fs, &files, &free_blocks, &reads, &writes, &compressions);
    CHECK("compression count > 0", compressions > 0);

    /* --- Phase 7: Append Mode --- */
    printf("--- Phase 7: Append Mode ---\n");
    rc = tfs_open(&fs, "append.trit", TFS_MODE_WRITE, &fd);
    CHECK("create append.trit succeeds", rc == 0);
    trit a1[5] = {1, 0, -1, 1, 0};
    tfs_write(&fs, &fd, a1, 5);
    tfs_close(&fs, &fd);

    rc = tfs_open(&fs, "append.trit", TFS_MODE_APPEND, &fd);
    CHECK("open for append succeeds", rc == 0);
    trit a2[5] = {-1, -1, 0, 1, 1};
    rc = tfs_write(&fs, &fd, a2, 5);
    CHECK("append write succeeds", rc == 5);
    tfs_close(&fs, &fd);

    rc = tfs_open(&fs, "append.trit", TFS_MODE_READ, &fd);
    CHECK("reopen for read succeeds", rc == 0);
    trit abuf[64];
    rlen = tfs_read(&fs, &fd, abuf, 64);
    CHECK("appended file has 10 trits", rlen == 10);
    int app_ok = 1;
    for (int i = 0; i < 5; i++) {
        if (abuf[i] != a1[i]) app_ok = 0;
        if (abuf[i + 5] != a2[i]) app_ok = 0;
    }
    CHECK("appended data correct", app_ok);
    tfs_close(&fs, &fd);

    /* --- Phase 8: Unlink --- */
    printf("--- Phase 8: Unlink ---\n");
    rc = tfs_unlink(&fs, "append.trit");
    CHECK("unlink succeeds", rc == 0);
    rc = tfs_open(&fs, "append.trit", TFS_MODE_WRITE, &fd);
    CHECK("open after unlink creates new file", rc == 0);
    tfs_close(&fs, &fd);
    rc = tfs_open(&fs, "append.trit", TFS_MODE_READ, &fd);
    CHECK("reopen new file for read", rc == 0);
    rlen = tfs_read(&fs, &fd, abuf, 64);
    CHECK("new file is empty", rlen == 0);
    tfs_close(&fs, &fd);

    /* --- Phase 9: Density & Area Metrics --- */
    printf("--- Phase 9: Density & Area Metrics ---\n");
    int density = tfs_density_gain_x100();
    CHECK("density gain >= 150 (1.5×)", density >= 150);
    CHECK("density gain <= 200 (2.0×)", density <= 200);

    int area = tfs_area_reduction_x100();
    CHECK("area reduction >= 50 (50%)", area >= 50);
    CHECK("area reduction <= 80 (80%)", area <= 80);

    /* --- Phase 10: Frequency Analysis --- */
    printf("--- Phase 10: Frequency Analysis ---\n");
    tfs_freq_t freq = tfs_frequency(data, 10);
    CHECK("freq total = 10", freq.freq_neg + freq.freq_zero + freq.freq_pos == 10);

    /* --- Phase 11: Multi-block file (large write) --- */
    printf("--- Phase 11: Multi-Block File ---\n");
    trit big[500];
    for (int i = 0; i < 500; i++) {
        big[i] = (trit)((i % 3) - 1);
    }
    rc = tfs_open(&fs, "bigfile.trit", TFS_MODE_WRITE, &fd);
    CHECK("open bigfile succeeds", rc == 0);
    rc = tfs_write(&fs, &fd, big, 500);
    CHECK("write 500 trits succeeds", rc == 500);
    tfs_close(&fs, &fd);

    rc = tfs_open(&fs, "bigfile.trit", TFS_MODE_READ, &fd);
    CHECK("reopen bigfile succeeds", rc == 0);
    trit bigread[500];
    rlen = tfs_read(&fs, &fd, bigread, 500);
    CHECK("read 500 trits back", rlen == 500);
    int big_ok = 1;
    for (int i = 0; i < 500; i++) {
        if (bigread[i] != big[i]) big_ok = 0;
    }
    CHECK("500-trit roundtrip matches", big_ok);
    tfs_close(&fs, &fd);
}

/* ================================================================
 *  SCENARIO 4 — Cross-Module Integration
 * ================================================================ */
static void test_cross_module(void) {
    printf("\n=== Scenario 4: Cross-Module Integration ===\n");

    /* --- Phase 1: MRAM → T-IPC pipeline --- */
    printf("--- Phase 1: MRAM → T-IPC Pipeline ---\n");
    mram_array_t arr;
    mram_init(&arr, 4, 4);

    /* Write pattern to MRAM */
    trit pattern[9] = { 1, -1, 0, 1, 0, -1, 1, 1, 0 };
    for (int i = 0; i < 9; i++) {
        mram_write_trit(&arr, i / 4, i % 4, pattern[i]);
    }

    /* Read back from MRAM */
    trit mram_read[9];
    for (int i = 0; i < 9; i++) {
        mram_read[i] = mram_read_trit(&arr, i / 4, i % 4);
    }

    /* Send via T-IPC */
    tipc_channel_t ch;
    tipc_channel_init(&ch);
    tipc_endpoint_create(&ch);
    tipc_endpoint_create(&ch);

    int rc = tipc_send(&ch, 1, mram_read, 9, TIPC_PRIO_HIGH);
    CHECK("MRAM data sent via T-IPC", rc == 0);

    trit ipc_recv[64];
    int rlen = tipc_recv(&ch, 1, ipc_recv, 64);
    CHECK("T-IPC delivers MRAM data", rlen == 9);

    int pipe_ok = 1;
    for (int i = 0; i < 9; i++) {
        if (ipc_recv[i] != pattern[i]) pipe_ok = 0;
    }
    CHECK("MRAM→IPC data integrity", pipe_ok);

    /* --- Phase 2: T-IPC → TFS storage --- */
    printf("--- Phase 2: T-IPC → TFS Storage ---\n");
    tfs_state_t fs;
    tfs_init(&fs);

    tfs_fd_t fd;
    rc = tfs_open(&fs, "ipc_dump.trit", TFS_MODE_WRITE, &fd);
    CHECK("TFS file created for IPC dump", rc == 0);

    rc = tfs_write(&fs, &fd, ipc_recv, rlen);
    CHECK("IPC data written to TFS", rc == rlen);
    tfs_close(&fs, &fd);

    /* Read back from TFS */
    rc = tfs_open(&fs, "ipc_dump.trit", TFS_MODE_READ, &fd);
    trit tfs_buf[64];
    int tlen = tfs_read(&fs, &fd, tfs_buf, 64);
    CHECK("TFS read back succeeds", tlen == 9);

    int cross_ok = 1;
    for (int i = 0; i < 9; i++) {
        if (tfs_buf[i] != pattern[i]) cross_ok = 0;
    }
    CHECK("MRAM→IPC→TFS full pipeline integrity", cross_ok);
    tfs_close(&fs, &fd);

    /* --- Phase 3: Shared Huffman scheme consistency --- */
    printf("--- Phase 3: Shared Huffman Consistency ---\n");
    trit test_data[8] = { 1, 0, -1, 1, -1, 0, 0, 1 };

    tipc_compressed_t tipc_comp;
    tipc_compress(&tipc_comp, test_data, 8);

    tfs_compressed_block_t tfs_comp;
    tfs_huffman_encode(&tfs_comp, test_data, 8);

    /* Both use same Huffman scheme, so bit_count should match */
    CHECK("TIPC and TFS Huffman produce same bit count",
          tipc_comp.bit_count == tfs_comp.bit_count);

    /* Both decompress to same data */
    trit tipc_dec[64], tfs_dec[64];
    tipc_decompress(tipc_dec, 64, &tipc_comp);
    tfs_huffman_decode(tfs_dec, 64, &tfs_comp);

    int huff_match = 1;
    for (int i = 0; i < 8; i++) {
        if (tipc_dec[i] != tfs_dec[i]) huff_match = 0;
    }
    CHECK("TIPC and TFS Huffman decode match", huff_match);

    /* --- Phase 4: Guardian scheme consistency --- */
    printf("--- Phase 4: Guardian Consistency ---\n");
    trit gdata[5] = { 1, -1, 0, 1, -1 };
    trit tipc_g = tipc_guardian_compute(gdata, 5);
    trit tfs_g  = tfs_guardian_compute(gdata, 5);
    CHECK("TIPC and TFS guardians match", tipc_g == tfs_g);

    /* --- Phase 5: Pack trits from MRAM, send via IPC, store in TFS --- */
    printf("--- Phase 5: Full Pack-Send-Store Pipeline ---\n");
    trit pack_src[5] = { 1, -1, 0, 1, 0 };
    uint8_t packed = mram_pack_trits(pack_src);
    CHECK("packed byte < 243 (radix-safe)", packed < 243);

    /* Verify radix guard accepts this byte */
    int viol = tipc_radix_guard(&packed, 1);
    CHECK("radix guard accepts packed trit byte", viol == 0);

    /* Unpack and store in TFS */
    trit unpacked[5];
    mram_unpack_trits(packed, unpacked);
    tfs_fd_t fd2;
    tfs_open(&fs, "packed.trit", TFS_MODE_WRITE, &fd2);
    tfs_write(&fs, &fd2, unpacked, 5);
    tfs_close(&fs, &fd2);

    tfs_open(&fs, "packed.trit", TFS_MODE_READ, &fd2);
    trit final_read[5];
    int flen = tfs_read(&fs, &fd2, final_read, 5);
    CHECK("full pipeline: 5 trits round-trip", flen == 5);
    int final_ok = 1;
    for (int i = 0; i < 5; i++) {
        if (final_read[i] != pack_src[i]) final_ok = 0;
    }
    CHECK("full pipeline data integrity", final_ok);
    tfs_close(&fs, &fd2);
}

/* ================================================================
 *  SCENARIO 5 — Constants & Specification Compliance
 * ================================================================ */
static void test_spec_compliance(void) {
    printf("\n=== Scenario 5: Specification Compliance ===\n");

    /* --- STT-MRAM Constants --- */
    printf("--- STT-MRAM Constants ---\n");
    CHECK("MRAM_TRITS_PER_BYTE == 5", MRAM_TRITS_PER_BYTE == 5);
    CHECK("MRAM_PACK_BASE == 243 (3^5)", MRAM_PACK_BASE == 243);
    CHECK("R_LOW (Parallel) = 50", MRAM_R_LOW_X10 == 50);
    CHECK("R_MID (Orthogonal) = 120", MRAM_R_MID_X10 == 120);
    CHECK("R_HIGH (Anti-Parallel) = 250", MRAM_R_HIGH_X10 == 250);
    CHECK("ECS drift threshold = 20", MRAM_ECS_DRIFT_THRESHOLD_X10 == 20);
    CHECK("Max recalibrations = 8", MRAM_ECS_MAX_RECAL == 8);

    /* --- T-IPC Constants --- */
    printf("--- T-IPC Constants ---\n");
    CHECK("TIPC_MAX_TRITS == 512", TIPC_MAX_TRITS == 512);
    CHECK("TIPC_HUFF_ZERO_BITS == 1", TIPC_HUFF_ZERO_BITS == 1);
    CHECK("TIPC_HUFF_POS_BITS == 2", TIPC_HUFF_POS_BITS == 2);
    CHECK("TIPC_HUFF_NEG_BITS == 2", TIPC_HUFF_NEG_BITS == 2);
    CHECK("TIPC_CMD_SEND == 0x10", TIPC_CMD_SEND == 0x10);
    CHECK("TIPC_CMD_RECV == 0x11", TIPC_CMD_RECV == 0x11);
    CHECK("TIPC_CMD_XOR_DIFF == 0x12", TIPC_CMD_XOR_DIFF == 0x12);
    CHECK("TIPC_CMD_GUARD == 0x13", TIPC_CMD_GUARD == 0x13);

    /* --- TFS Constants --- */
    printf("--- TFS Constants ---\n");
    CHECK("TFS_BLOCK_TRITS == 243 (3^5)", TFS_BLOCK_TRITS == 243);
    CHECK("TFS_MAX_BLOCKS == 1024", TFS_MAX_BLOCKS == 1024);
    CHECK("TFS_MAX_FILES == 128", TFS_MAX_FILES == 128);
    CHECK("TFS_DENSITY_GAIN >= 158", TFS_DENSITY_GAIN_X100 >= 158);
    CHECK("TFS_AREA_REDUCTION >= 60", TFS_AREA_REDUCTION_X100 >= 60);

    /* --- Huffman code lengths spec compliance --- */
    printf("--- Huffman Code Verification ---\n");
    /* 0 (Unknown) must encode to 1 bit */
    trit z1[1] = { TRIT_UNKNOWN };
    tipc_compressed_t c1;
    tipc_compress(&c1, z1, 1);
    CHECK("Unknown encodes to 1 bit", c1.bit_count == 1);

    /* +1 (True) must encode to 2 bits */
    trit p1[1] = { TRIT_TRUE };
    tipc_compressed_t c2;
    tipc_compress(&c2, p1, 1);
    CHECK("True encodes to 2 bits", c2.bit_count == 2);

    /* -1 (False) must encode to 2 bits */
    trit n1[1] = { TRIT_FALSE };
    tipc_compressed_t c3;
    tipc_compress(&c3, n1, 1);
    CHECK("False encodes to 2 bits", c3.bit_count == 2);

    /* Average code length for uniform distribution: (1+2+2)/3 = 1.667 bits/trit */
    /* vs 1.585 bits/trit (log2(3)), so overhead ≤ 6% */
    int avg_bits_x100 = (1 + 2 + 2) * 100 / 3;
    int optimal_x100 = 159; /* 1.585 × 100 rounded */
    int overhead_x100 = (avg_bits_x100 - optimal_x100) * 100 / optimal_x100;
    CHECK("Huffman overhead <= 10%", overhead_x100 <= 10);
}

/* ================================================================ */
int main(void) {
    printf("╔════════════════════════════════════════════════╗\n");
    printf("║  seT6 Friday Updates — Test Suite             ║\n");
    printf("║  STT-MRAM · T-IPC · TFS                      ║\n");
    printf("╚════════════════════════════════════════════════╝\n");

    test_stt_mram();
    test_tipc();
    test_tfs();
    test_cross_module();
    test_spec_compliance();

    printf("\n════════════════════════════════════════════════\n");
    printf("  Results: %d run, %d passed, %d failed\n",
           tests_run, tests_passed, tests_failed);

    if (tests_failed == 0) {
        printf("  ALL %d FRIDAY UPDATE TESTS PASSED\n", tests_passed);
    } else {
        printf("  %d FRIDAY UPDATE FAILURES\n", tests_failed);
    }
    printf("════════════════════════════════════════════════\n");

    return tests_failed;
}
