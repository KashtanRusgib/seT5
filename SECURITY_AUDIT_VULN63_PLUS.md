# seT5 Security Audit — VULN-63 through VULN-79

**Date:** 2025-07-10
**Scope:** Red-team exercise on all source files in `/workspaces/seT5`
**Prior art:** VULN-01 through VULN-62 already patched — not re-reported.
**Auditor model:** Claude Opus 4.6 (GitHub Copilot)

---

## Summary

| Severity | Count |
|----------|-------|
| Critical | 3     |
| High     | 7     |
| Medium   | 5     |
| Low      | 2     |
| **Total**| **17**|

Attack-class coverage:

| Category | VULNs |
|----------|-------|
| Memory Safety | 63, 64, 65, 66, 70, 76 |
| Integer Vulnerabilities | 64, 67 |
| Injection / Confusion | 75 |
| Logic Flaws | 74, 78 |
| Cryptographic Weakness | 73, 79 |
| Concurrency | 69 |
| Resource Exhaustion / DoS | 71 |
| Ternary-Specific | 72 |
| Info Leak | 68 |
| Authorization Bypass | 77, 78 |

---

## VULN-63 — Parser: Four Unguarded `realloc()` Calls

| Field | Value |
|-------|-------|
| **File** | `tools/compiler/src/parser.c` lines 497, 557, 648, 689 |
| **Severity** | High |
| **Class** | Memory Safety — NULL dereference / Memory leak |

**Vulnerable code** (line 497, representative of all four):

```c
init_count++;
init_vals = (Expr **)realloc(init_vals, init_count * sizeof(Expr *));
init_vals[init_count - 1] = parse_expr_r();
```

**Exploit scenario:** An attacker supplies a source file with a large array
initializer or deeply nested function definitions. When the host is under
memory pressure, `realloc()` returns `NULL`. The old pointer is leaked, and
the immediate dereference (`init_vals[init_count - 1] = …`) writes through a
NULL pointer — a segfault at best, or, on systems where NULL-page mapping is
possible (e.g., older Linux kernels or embedded targets), arbitrary code
execution via controlled writes to address 0.

**Fix** (apply at each of the four sites — lines 497, 557, 648, 689):

```c
// Replace:
init_vals = (Expr **)realloc(init_vals, init_count * sizeof(Expr *));
// With:
Expr **new_vals = (Expr **)realloc(init_vals, init_count * sizeof(Expr *));
if (!new_vals) {
    parser_error("out of memory");
    for (int k = 0; k < init_count - 1; k++) expr_free(init_vals[k]);
    free(init_vals);
    free(vname);
    return NULL;
}
init_vals = new_vals;
```

---

## VULN-64 — ai_acceleration.c: Integer Overflow in Sparse Matrix Allocation

| Field | Value |
|-------|-------|
| **File** | `src/ai_acceleration.c` line 250 |
| **Severity** | Critical |
| **Class** | Integer Overflow → Heap Buffer Overflow |

**Vulnerable code:**

```c
int max_possible_nnz = (rows * cols * max_nz) / block_size;
matrix->values      = malloc(max_possible_nnz * sizeof(trit));
matrix->row_indices  = malloc(max_possible_nnz * sizeof(int));
matrix->col_indices  = malloc(max_possible_nnz * sizeof(int));
```

**Exploit scenario:** If an attacker controls layer dimensions (e.g., via a
loaded model file), setting `rows=65536, cols=65536, max_nz=2` gives
`rows * cols * max_nz = 8,589,934,592` which overflows signed 32-bit int to a
small/negative value. `malloc()` allocates a tiny buffer — subsequent
`sparse_trit_populate()` writes thousands of entries past that buffer into the
heap, enabling heap metadata corruption and arbitrary code execution.

**Fix:**

```c
// Replace:
int max_possible_nnz = (rows * cols * max_nz) / block_size;
// With:
int64_t nnz64 = ((int64_t)rows * cols * max_nz) / block_size;
if (nnz64 > INT_MAX || nnz64 <= 0) { free(matrix); return NULL; }
int max_possible_nnz = (int)nnz64;
```

---

## VULN-65 — ternary_database.c: OOB Read — Missing `col_idx` Bounds Check

| Field | Value |
|-------|-------|
| **File** | `src/ternary_database.c` ~line 515 |
| **Severity** | High |
| **Class** | Memory Safety — Out-of-Bounds Read |

**Vulnerable code:**

```c
int ternary_db_select_where(ternary_database_t *db, int col_idx,
                           trit condition_value,
                           trit *result_rows[TERNARY_DB_MAX_ROWS]) {
    int result_count = 0;
    for (int row = 0; row < db->num_rows; row++) {
        trit cell_value = db->data[row][col_idx];     /* OOB if col_idx out of range */
        trit is_null = db->null_mask[row][col_idx];   /* OOB */
```

**Exploit scenario:** A caller passes `col_idx = -1` or
`col_idx >= TERNARY_DB_MAX_COLS (16)`. Since `data` and `null_mask` are
fixed-width 2D arrays, negative indices read from the preceding struct member,
and indices ≥ 16 read into `null_mask` (or past the array entirely). An
attacker who controls a SQL-like query column index can leak adjacent struct
memory or cross row boundaries to recover data from other rows — an
information disclosure primitive.

**Fix:**

```c
int ternary_db_select_where(ternary_database_t *db, int col_idx,
                           trit condition_value,
                           trit *result_rows[TERNARY_DB_MAX_ROWS]) {
    if (!db || col_idx < 0 || col_idx >= db->num_cols) return -1;
    int result_count = 0;
    // ... rest unchanged
```

---

## VULN-66 — ternary_database.c: `num_cols` Unchecked in `db_init` → Stack/Heap Overflow

| Field | Value |
|-------|-------|
| **File** | `src/ternary_database.c` ~line 487 |
| **Severity** | High |
| **Class** | Memory Safety — Buffer Overflow via Unchecked Size |

**Vulnerable code:**

```c
void ternary_db_init(ternary_database_t *db, int num_cols,
                     ternary_null_mode_t null_mode) {
    memset(db, 0, sizeof(*db));
    db->num_cols = num_cols;   /* No validation against TERNARY_DB_MAX_COLS */
    db->null_mode = null_mode;
}
```

Then in `ternary_db_insert()`:

```c
memcpy(db->data[db->num_rows], row_data, db->num_cols * sizeof(trit));
```

**Exploit scenario:** Calling `ternary_db_init(db, 1000, ...)` stores 1000 in
`num_cols`. The first `ternary_db_insert()` copies 1000 trits into
`db->data[0]`, which is only 16 trits wide. The 984 extra bytes overflow
into `null_mask`, then `num_rows`, `num_cols`, `null_mode` — overwriting
control fields. An attacker can then manipulate `null_mode` to affect query
semantics or set `num_cols` to enable further overflow chains.

**Fix:**

```c
void ternary_db_init(ternary_database_t *db, int num_cols,
                     ternary_null_mode_t null_mode) {
    memset(db, 0, sizeof(*db));
    if (num_cols < 1)  num_cols = 1;
    if (num_cols > TERNARY_DB_MAX_COLS) num_cols = TERNARY_DB_MAX_COLS;
    db->num_cols = num_cols;
    db->null_mode = null_mode;
}
```

---

## VULN-67 — tipc.c: Integer Overflow in `tipc_compression_ratio()`

| Field | Value |
|-------|-------|
| **File** | `src/tipc.c` ~line 224 |
| **Severity** | Medium |
| **Class** | Integer Overflow → Division by Zero / Wrong Result |

**Vulnerable code:**

```c
int tipc_compression_ratio(const tipc_compressed_t *comp) {
    if (!comp || comp->original_trits <= 0 || comp->bit_count <= 0)
        return -1;
    int raw_bits_x1000 = comp->original_trits * 1585;
    if (raw_bits_x1000 == 0) return -1;
    return (comp->bit_count * 1000 * 1000) / raw_bits_x1000;
}
```

**Exploit scenario:** `comp->bit_count * 1000 * 1000` overflows `int` when
`bit_count > 2147` (since `INT_MAX ≈ 2.1×10⁹`). Similarly,
`original_trits * 1585` overflows when `original_trits > 1,354,474`. On
overflow, intermediate values may become negative or zero. A zero intermediate
causes a division-by-zero crash; a sign flip produces a bogus ratio that
downstream logic (e.g., compression threshold decisions) might interpret as
"excellent compression", leading to data being stored in a corrupted
compressed form.

**Fix:**

```c
int tipc_compression_ratio(const tipc_compressed_t *comp) {
    if (!comp || comp->original_trits <= 0 || comp->bit_count <= 0)
        return -1;
    int64_t raw  = (int64_t)comp->original_trits * 1585;
    if (raw == 0) return -1;
    int64_t ratio = ((int64_t)comp->bit_count * 1000000) / raw;
    if (ratio > INT_MAX) return INT_MAX;
    return (int)ratio;
}
```

---

## VULN-68 — tbe_main.c: Stack Information Leak via Past-Terminator Read

| Field | Value |
|-------|-------|
| **File** | `src/tbe_main.c` ~line 559, 565 |
| **Severity** | Low |
| **Class** | Information Leak — Out-of-Bounds Read |

**Vulnerable code** ("trithon" command):

```c
} else if (strcmp(cmd, "trithon") == 0) {
    const char *expr = line + 8;   /* "trithon" = 7 chars */
    while (*expr == ' ') expr++;
    tbe_trithon_call(expr);
```

And "echo" command:

```c
} else if (strcmp(cmd, "echo") == 0) {
    const char *text = line + 5;   /* "echo" = 4 chars */
    while (*text == ' ') text++;
    printf("%s\n", text);
```

**Exploit scenario:** When input arrives via pipe without a trailing newline
(e.g., `echo -n "trithon" | ./tbe`), `fgets()` stores `"trithon\0"` — 8
bytes. `line + 8` points one byte past the null terminator into
uninitialized stack memory (`line[512]` is a local array). The `while` loop
and subsequent `printf` / `tbe_trithon_call` read and print stack contents
until the next null byte. An attacker with pipe access can extract stack data
(return addresses, saved registers, prior command content) from the TBE
process.

**Fix:**

```c
} else if (strcmp(cmd, "trithon") == 0) {
    const char *expr = line + strlen("trithon");
    if (*expr == '\0') { printf("Usage: trithon <expr>\n"); }
    else { while (*expr == ' ') expr++; tbe_trithon_call(expr); }

} else if (strcmp(cmd, "echo") == 0) {
    const char *text = line + strlen("echo");
    if (*text == '\0') { printf("\n"); }
    else { while (*text == ' ') text++; printf("%s\n", text); }
```

---

## VULN-69 — memory.c: TOCTOU Race in `mem_alloc()` — Double Allocation

| Field | Value |
|-------|-------|
| **File** | `src/memory.c` lines 53–64 |
| **Severity** | High |
| **Class** | Concurrency — Time-of-Check-to-Time-of-Use |

**Vulnerable code:**

```c
int mem_alloc(set5_mem_t *mem, int owner_tid) {
    if (!mem) return -1;
    for (int p = 0; p < mem->total_pages; p++) {
        if (mem->pages[p].valid == TRIT_UNKNOWN) {  /* CHECK */
            set5_page_t *pg = &mem->pages[p];
            pg->valid     = TRIT_TRUE;               /* USE */
            pg->owner_tid = owner_tid;
```

**Exploit scenario:** On a multi-core system, two threads call `mem_alloc()`
simultaneously. Both scan the page array and find the same free page (valid ==
TRIT_UNKNOWN). Both set it to TRIT_TRUE with their own `owner_tid`. The second
write silently overwrites the first owner. Both threads now believe they
exclusively own page `p`. When thread A writes secret data, thread B reads the
same physical page — a cross-process data leak. The same TOCTOU exists in
`mem_free` (double-free), `mem_reserve`, and all IPC/scheduler functions.

**Fix:**

```c
/* Add a spinlock or atomic compare-and-swap: */
int mem_alloc(set5_mem_t *mem, int owner_tid) {
    if (!mem) return -1;
    spinlock_acquire(&mem->lock);
    for (int p = 0; p < mem->total_pages; p++) {
        if (mem->pages[p].valid == TRIT_UNKNOWN) {
            mem->pages[p].valid     = TRIT_TRUE;
            mem->pages[p].owner_tid = owner_tid;
            mem->pages[p].ref_count = 1;
            mem->free_count--;
            mem->alloc_count++;
            spinlock_release(&mem->lock);
            return p;
        }
    }
    spinlock_release(&mem->lock);
    return -1;
}
```

---

## VULN-70 — samsung_tbn.c: `ss_zid_detect()` OOB Write to Stack Bitmap

| Field | Value |
|-------|-------|
| **File** | `src/samsung_tbn.c` ~line 140 |
| **Severity** | High |
| **Class** | Memory Safety — Stack Buffer Overflow |

**Vulnerable code:**

```c
void ss_zid_detect(const ss_input_t *vector, int size,
                   uint32_t *bitmap, int num_words) {
    memset(bitmap, 0, (size_t)num_words * sizeof(uint32_t));
    for (int i = 0; i < size; i++) {
        if (vector[i] != SS_ZERO) {
            int word_idx = i / 32;
            int bit_idx  = i % 32;
            bitmap[word_idx] |= (1u << bit_idx);  /* No word_idx < num_words check */
```

Called from `ss_matmul_ternary_tbn()`:

```c
uint32_t zid_bitmap[8]; /* 256 bits max */
ss_zid_detect(layer->weights_input[row], size, zid_bitmap, 8);
```

**Exploit scenario:** If `size` exceeds `num_words * 32` (i.e., more than 256
input elements when `num_words=8`), `word_idx` exceeds 7 and the write goes
past the end of the stack-allocated `zid_bitmap[8]`. This overwrites adjacent
stack variables (loop counter, return address). An attacker who controls the
neural network layer topology (via model file) can set `input_size > 256` and
overwrite the return address for arbitrary code execution.

**Fix:**

```c
for (int i = 0; i < size; i++) {
    if (vector[i] != SS_ZERO) {
        int word_idx = i / 32;
        if (word_idx >= num_words) break;  /* Bounds check */
        int bit_idx  = i % 32;
        bitmap[word_idx] |= (1u << bit_idx);
    }
}
```

---

## VULN-71 — parser.c: Unbounded Recursion Depth → Stack Overflow DoS

| Field | Value |
|-------|-------|
| **File** | `tools/compiler/src/parser.c` — `parse_expr_r()` |
| **Severity** | Medium |
| **Class** | Resource Exhaustion / Denial of Service |

**Vulnerable code** (recursive call chain):

```c
static Expr *parse_expr_r(void) {
    // ...
    Expr *left = parse_expr_r();  /* Recursive descent for subexpressions */
    // ...
    // Also: parse_stmt() → parse_expr_r() → parse_stmt() → ...
}
```

**Exploit scenario:** A malicious `.tri` source file containing deeply nested
parenthesized expressions — e.g., `((((((((((((((1))))))))))))))` repeated
10,000 times — causes `parse_expr_r()` to recurse ~10,000 times. Each frame
consumes stack space for local variables and return addresses. On a typical
8 MB stack, ~50,000–100,000 frames cause a segfault. The compiler crashes
without any error message. If the compiler is invoked by a build system or CI
pipeline, this is a DoS vector.

**Fix:**

```c
#define PARSER_MAX_DEPTH 256
static int parse_depth = 0;

static Expr *parse_expr_r(void) {
    if (++parse_depth > PARSER_MAX_DEPTH) {
        parser_error("expression nesting too deep");
        parse_depth--;
        return NULL;
    }
    // ... existing code ...
    parse_depth--;
    return result;
}
```

---

## VULN-72 — trit_emu.h: Fault Trit Silently Clamped to Zero

| Field | Value |
|-------|-------|
| **File** | `include/set5/trit_emu.h` ~line 74 |
| **Severity** | Medium |
| **Class** | Ternary-Specific — Error Masking |

**Vulnerable code:**

```c
static inline int trit2_decode(trit2 t) {
    static const int lut[4] = { -1, 0, 0 /* fault->clamp */, 1 };
    return lut[t & 0x03];
}
```

The encoding is: `00=-1 (F)`, `01=0 (U)`, `10=fault`, `11=+1 (T)`.

**Exploit scenario:** A hardware fault or memory corruption flips a bit in a
packed `trit2_reg32`, producing `10` (fault) encoding. Instead of trapping or
signaling the fault, `trit2_decode()` silently returns 0 (TRIT_UNKNOWN).
Downstream logic treats the corrupted trit as a valid "unknown" value. In a
security context (e.g., capability validity), TRIT_UNKNOWN means "pending" —
which some access-check paths may grant. An attacker who can induce targeted
bit-flips (Rowhammer, voltage glitching) can flip a TRIT_FALSE (denied, `00`)
to fault (`10`), which decodes as 0/UNKNOWN, potentially upgrading a denied
capability to a pending/sandboxed one.

**Fix:**

```c
static inline int trit2_decode(trit2 t) {
    /* Encoding: 00=-1, 01=0, 11=+1, 10=FAULT */
    if ((t & 0x03) == TRIT2_FAULT) return TRIT2_FAULT_SIGNAL; /* -128 sentinel */
    static const int lut[4] = { -1, 0, 0, 1 };
    return lut[t & 0x03];
}
/* Callers must check: if (trit2_decode(t) == TRIT2_FAULT_SIGNAL) handle_fault(); */
```

---

## VULN-73 — trit_crypto.c: NULL IV Defaults to All-Zero → Deterministic Keystream

| Field | Value |
|-------|-------|
| **File** | `src/trit_crypto.c` lines 247–250 |
| **Severity** | High |
| **Class** | Cryptographic Weakness — Nonce Reuse |

**Vulnerable code:**

```c
void tcrypto_cipher_init(tcrypto_cipher_t *c, const tcrypto_key_t *key,
                          const trit *iv, int rounds) {
    if (!c || !key) return;
    c->key    = *key;
    c->rounds = (rounds > 0) ? rounds : 12;
    if (iv)
        memcpy(c->iv, iv, TCRYPTO_MAC_TRITS * sizeof(trit));
    else
        memset(c->iv, 0, TCRYPTO_MAC_TRITS * sizeof(trit));  /* ← all-zero IV */
}
```

**Exploit scenario:** Any caller who passes `iv = NULL` (the "easy" API path)
gets an all-zero IV. Because the CTR-mode offset (VULN-40 fix) is derived
from `c->iv[iv_idx]`, an all-zero IV makes `ctr_iv = ctr_offset` —
deterministic. Encrypting two messages with the same key and NULL IV
produces identical keystreams. XOR-ing the two ciphertexts yields the XOR of
the two plaintexts (crib-dragging attack). For a 27-trit IV with only
3^27 ≈ 7.6×10¹² possible values, even a random IV is weak; but an all-zero
IV is catastrophic.

**Fix:**

```c
void tcrypto_cipher_init(tcrypto_cipher_t *c, const tcrypto_key_t *key,
                          const trit *iv, int rounds) {
    if (!c || !key) return;
    c->key    = *key;
    c->rounds = (rounds > 0) ? rounds : 12;
    if (iv) {
        memcpy(c->iv, iv, TCRYPTO_MAC_TRITS * sizeof(trit));
    } else {
        /* VULN-73 fix: reject NULL IV — callers MUST provide unique nonce */
        fprintf(stderr, "tcrypto: IV required; refusing NULL IV\n");
        memset(c, 0, sizeof(*c));  /* Poison cipher state */
        return;
    }
}
```

---

## VULN-74 — namespace_isolation.c: Root Namespace Bypasses All Access Checks

| Field | Value |
|-------|-------|
| **File** | `src/namespace_isolation.c` ~line 108 |
| **Severity** | Medium |
| **Class** | Logic Flaw — Privilege Escalation |

**Vulnerable code:**

```c
static inline int ns_check_access(ns_state_t *s, int proc_idx, int target_ns) {
    // ...
    ns_process_t *p = &s->processes[proc_idx];

    /* Root namespace has full access */
    if (p->namespace_id == 0) return NS_ACCESS_GRANTED;
```

**Exploit scenario:** Despite VULN-62 requiring `NS_CAP_ROOT_NS` to spawn
into the root namespace, any process that legitimately exists in namespace 0
(e.g., a system daemon) gets unconditional access to ALL other namespaces.
There is no capability check for cross-namespace access even for root-namespace
processes. If an attacker compromises any root-namespace process (e.g., via a
memory corruption bug in another module), they inherit unrestricted access to
every namespace — violating the principle of least privilege that
capability-based isolation is designed to enforce.

**Fix:**

```c
/* Root namespace should still require explicit cross-namespace capabilities */
if (p->namespace_id == 0) {
    if (target_ns == 0) return NS_ACCESS_GRANTED; /* same namespace */
    /* Cross-namespace: require capability even for root */
    if (p->capabilities & s->namespaces[target_ns].type_mask)
        return NS_ACCESS_SANDBOXED;
    s->total_violations++;
    p->violations++;
    return NS_ACCESS_DENIED;
}
```

---

## VULN-75 — godel_machine.c: Switchprog Path Traversal → Arbitrary File Write

| Field | Value |
|-------|-------|
| **File** | `src/godel_machine.c` ~line 312 |
| **Severity** | Critical |
| **Class** | Injection — Path Traversal |

**Vulnerable code:**

```c
int godel_set_switchprog(godel_machine_t *gm, const char *filepath,
                        const char *old_content, const char *new_content) {
    // ...
    snprintf(sp->filepath, sizeof(sp->filepath), "%s", filepath);
```

**Exploit scenario:** The `filepath` parameter is stored without any path
validation — no check for `..`, no canonicalization, no chroot-relative
enforcement. When the RSI flywheel later applies the switchprog (replacing
`old_content` with `new_content` in the file), an attacker who can influence
the proof search input can set
`filepath = "../../../../etc/crontab"` and inject a cron entry. Since the
Gödel machine is designed to self-modify, the write mechanism is intentional —
but the lack of path confinement means the self-modification scope is
unbounded.

**Fix:**

```c
int godel_set_switchprog(godel_machine_t *gm, const char *filepath,
                        const char *old_content, const char *new_content) {
    // ...
    /* VULN-75 fix: reject path traversal */
    if (strstr(filepath, "..") != NULL) return -1;
    if (filepath[0] == '/') return -1;  /* Must be relative */
    /* Confine to allowed mutation zones */
    if (!zone_check(filepath)) return -1;
    snprintf(sp->filepath, sizeof(sp->filepath), "%s", filepath);
```

---

## VULN-76 — codegen.c: `emit()` Has No Bounds Check → Buffer Overflow

| Field | Value |
|-------|-------|
| **File** | `tools/compiler/src/codegen.c` line 11 |
| **Severity** | Critical |
| **Class** | Memory Safety — Global Buffer Overflow |

**Vulnerable code:**

```c
unsigned char bytecode[MAX_BYTECODE];
size_t bc_idx = 0;

static void emit(unsigned char op) {
    bytecode[bc_idx++] = op;  /* No bounds check */
}
```

**Exploit scenario:** The `codegen()` function calls `emit()` twice per
integer operand (`OP_PUSH` + value) and once per operator. A source file with
> 2048 integer literals generates > 4096 emit calls, overflowing the
`bytecode[MAX_BYTECODE]` buffer (where `MAX_BYTECODE = 4096`). Since
`bytecode` is a global array, the overflow corrupts adjacent global variables
(`bc_idx` itself, then any subsequent globals). On most platforms, this enables
writing attacker-controlled bytes to arbitrary global memory. If the compiler
is used as part of a build pipeline that processes untrusted input, this is
remote code execution on the build host.

**Fix:**

```c
static int emit(unsigned char op) {
    if (bc_idx >= MAX_BYTECODE) {
        fprintf(stderr, "codegen: bytecode overflow at index %zu\n", bc_idx);
        return -1;
    }
    bytecode[bc_idx++] = op;
    return 0;
}
/* All callers must check return value and abort codegen on failure. */
```

---

## VULN-77 — syscall.c: LOAD_BALANCE Affinity Clamp Missing Upper Bound

| Field | Value |
|-------|-------|
| **File** | `src/syscall.c` ~line 273 |
| **Severity** | High |
| **Class** | Integer Vulnerability — OOB Index Planting |

**Vulnerable code:**

```c
case SYSCALL_LOAD_BALANCE:
    if (ks->sched.current_tid >= 0) {
        sched_set_priority(&ks->sched, ks->sched.current_tid,
                           trit_from_int(arg0));
        /* VULN-58 fix: clamp cpu_affinity to valid range. */
        int affinity = arg1;
        if (affinity < -1) affinity = -1;  /* clamp negative to 'any' */
        ks->sched.threads[ks->sched.current_tid].cpu_affinity = affinity;
    }
```

**Exploit scenario:** The VULN-58 fix only clamps values below -1 but imposes
no upper bound. A user-space thread calling `SYSCALL_LOAD_BALANCE` with
`arg1 = 0x7FFFFFFF` stores that value in `cpu_affinity`. If a future scheduler
extension (or existing load-balance code path) uses `cpu_affinity` as an array
index into a per-CPU structure (e.g., `cpu_queues[affinity]`), this gives a
massive OOB access. Even without that, a nonsensical affinity value breaks any
NUMA-aware scheduling logic.

**Fix:**

```c
int affinity = arg1;
if (affinity < -1) affinity = -1;
if (affinity >= SCHED_MAX_CPUS) affinity = -1; /* VULN-77 fix: upper bound */
ks->sched.threads[ks->sched.current_tid].cpu_affinity = affinity;
```

---

## VULN-78 — syscall.c: Capability Check Is Global, Not Per-Caller

| Field | Value |
|-------|-------|
| **File** | `src/syscall.c` ~lines 140–167 |
| **Severity** | High |
| **Class** | Logic Flaw — Authorization Bypass |

**Vulnerable code:**

```c
if (ks->cap_count > 0) {
    // ...
    if (need_right != 0) {
        int has_cap = 0;
        for (int ci = 0; ci < ks->cap_count; ci++) {
            if (kernel_cap_check(ks, ci, need_right)) {
                has_cap = 1;
                break;
            }
        }
        if (!has_cap) { /* deny */ }
    }
}
```

**Exploit scenario:** The VULN-38 fix added per-syscall capability
enforcement, but the check iterates the GLOBAL capability table — it never
verifies that the calling thread (identified by `ks->sched.current_tid`)
actually owns the matching capability. In a seL4-style microkernel,
capabilities must be unforgeable per-process references. Here, if Thread A
creates a capability with write rights, Thread B (an unprivileged attacker
thread with zero capabilities) can call `SYSCALL_MMAP` because the global
table scan finds Thread A's capability and grants access to everyone. This
is a complete authorization bypass for all privileged syscalls.

**Fix:**

```c
if (need_right != 0) {
    int caller_tid = ks->sched.current_tid;
    int has_cap = 0;
    for (int ci = 0; ci < ks->cap_count; ci++) {
        /* VULN-78 fix: bind capability check to calling thread */
        if (ks->caps[ci].object_id == caller_tid &&
            kernel_cap_check(ks, ci, need_right)) {
            has_cap = 1;
            break;
        }
    }
    if (!has_cap) { res.retval = -1; res.result_trit = TRIT_FALSE; return res; }
}
```

> **Note:** A full fix requires a per-thread CSpace (capability space) as in
> seL4, not just filtering the global table by `object_id`.

---

## VULN-79 — trit_crypto.c: Division by Zero if `key.length == 0`

| Field | Value |
|-------|-------|
| **File** | `src/trit_crypto.c` ~line 261 |
| **Severity** | Medium |
| **Class** | Cryptographic Weakness — Crash / Denial of Service |

**Vulnerable code:**

```c
void tcrypto_encrypt(tcrypto_cipher_t *c, trit *data, int len) {
    if (!c || !data || len <= 0) return;
    for (int round = 0; round < c->rounds; round++) {
        for (int i = 0; i < len; i++) {
            int key_idx = (i + round) % c->key.length;  /* div-by-zero if length == 0 */
            data[i] = tcrypto_trit_xor(data[i], c->key.data[key_idx]);
```

**Exploit scenario:** If `tcrypto_cipher_init()` is called with a
zero-initialized or corrupted key struct (where `key->length == 0`), the
modulo operation `% c->key.length` triggers undefined behavior (division by
zero on most architectures: SIGFPE crash). This is a DoS vector — an attacker
who can corrupt the key struct (e.g., via an adjacent buffer overflow)
crashes the crypto subsystem, potentially leaving sessions unencrypted.
The same pattern exists in `tcrypto_decrypt()`.

**Fix:**

```c
void tcrypto_encrypt(tcrypto_cipher_t *c, trit *data, int len) {
    if (!c || !data || len <= 0) return;
    if (c->key.length <= 0) return;  /* VULN-79 fix: reject zero-length key */
    // ...
```

Apply the same guard to `tcrypto_decrypt()`.

---

## Systemic Observations (Not Individually Numbered)

1. **No locking anywhere.** Every kernel data structure (`set5_mem_t`,
   `ipc_state_t`, `sched_state_t_state`, `kernel_state_t`) is accessed
   without mutual exclusion. VULN-69 is one instance, but the pattern affects
   ALL subsystems. A comprehensive spinlock/mutex strategy is needed before
   any SMP support.

2. **Trit values never validated at trust boundaries.** `trit` is `int8_t`,
   so any of 256 byte values can flow through IPC into kernel state. While
   individual functions handle out-of-range values via switch defaults, a
   systematic trit-validation barrier at the syscall entry point would
   prevent an entire class of confusion bugs.

3. **Static/global mutable state in compiler and VM.** The compiler
   (`codegen.c`: `bytecode[]`, `bc_idx`; `parser.c`: `tokens[]`, `pidx`) and
   VM (`ternary_vm.c`: `memory[]`, `stack[]`, `sp`, `ip`) use file-scope
   globals. This prevents safe concurrent compilation/execution and makes
   re-entrancy impossible.

---

## Files Audited

| Module | Files | Status |
|--------|-------|--------|
| Core kernel | memory.c, ipc.c, scheduler.c, syscall.c, namespace_isolation.c | ✅ Full |
| Security | trit_crypto.c, audit_firewall.c | ✅ Full |
| Gödel machine | godel_machine.c, godel_archive.c, godel_proof_searcher.c, godel_utility.c, godel_mutable_zones.c | ✅ Full |
| VM/Compiler | ternary_vm.c, codegen.c, parser.c | ✅ Full |
| Networking | fault_tolerant_network.c, time_sync_daemon.c, pam3_transcode.c | ✅ Full |
| Storage | tfs.c, ternary_database.c | ✅ Full |
| HAL | huawei_alu.c, samsung_tbn.c, stt_mram.c, ingole_talu.c | ✅ Full |
| AI | symbiotic_ai.c, ternary_snn.c, ai_acceleration.c | ✅ Full |
| Other | multiradix.c, trit_rns.c, radix_transcode.c, tbe_main.c, tipc.c | ✅ Full |
| Headers | include/set5/syscall.h, trit_crypto.h, posix.h, trit_emu.h, trit_ai.h | ✅ Full |

**End of report.**
