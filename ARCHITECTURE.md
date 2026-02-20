> **seT6 Purpose and Goal:** In seT6 we have implemented various schema(s) to build the ternary first full stack for the inevitable global shift to a fully ternary/multi radix world. The ongoing development of seT6 and Trit Linux & Trithon and all other features and modules and codeblocks that comprise the seT6 ternary first & ternary all the way down fullstack is to contiually determine the greatest imminent and emerging needs of the ternary/multi radix future that requires a complete rebuild and rethink of the flawed and faulty and error prone old world of binary based computing. This ongoing development seeks in all instances possible to conceive as fully as possible of the implications and needs of the entire computer hardware and software world and industires as the ternary/multi radix future emerges and to search for and find and research and understand all relevant hardware and software and protocol improvements and upgrades and components of this ternary/multi radix first world. From any and all available patents and papers and documentation the human & AI agents working on this development develop an empirical understanding of the hardware and software being developed and scheduled for market and industrial and governmental and medical and aerospace and AGI applications to futher the capbabilities and funcitonality and utility and value recieved by all users of seT6 by anticipating all needs current and future and thus developing seT6 to accomodate these new and improved ternary/multi radix archtectures and designs such that when the hardware arrives and when the protocols are instantiated the full ternary stack that is seT6 will already be available and tested and verified and at all times and in all decisions and choices made and code updates and commits this will be done and will only be done while maintaining the Sigma 9 level of rigorously tested and verifiable build quality resulting in 0 errors.
>
> *See also: [SET6_PURPOSE_AND_GOAL.md](SET6_PURPOSE_AND_GOAL.md)*

---

# seT5 Architecture — Secure Embedded Ternary Microkernel 5

> Last updated: 2026-02-14 — **seT5 FROZEN** — Architecture preserved, see `seT6/ARCHITECTURE.md` for active development

> ### ⚠️ FROZEN — seT5 architecture finalized
>
> seT5 achieved 0 errors and is preserved exactly as-is. The **seT6** fork (in
> `seT6/`) inherits this architecture and extends it with Arch Linux–inspired
> modularity, hardened comms, time sync, and attack-surface reduction.

> **⚠️ TEST GLOSSARY PROTOCOL**: Every new test MUST be logged in
> [`seT6/TESTS_GLOSSARY_OF_ALL_TESTS.md`](seT6/TESTS_GLOSSARY_OF_ALL_TESTS.md)
> before a commit is considered valid. Current: **6603+ runtime assertions**
> across **101 active test suites** (104 total including disabled). For the
> mandatory 4-step checklist when adding tests, see the glossary's "Rule:
> Future Test Documentation" section.

---

## 1. Overview

seT5 is a **ground-up rewrite of the seL4 verified microkernel** in balanced
ternary logic (Kleene's K₃).  Every value in the system — capabilities,
addresses, registers, IPC payloads — is a first-class **trit** with three
states: `{-1 (False), 0 (Unknown), +1 (True)}`.

**Design thesis:** Binary kernels lie — uninitialized memory defaults to `0`
which is indistinguishable from a valid zero.  In seT5, uninitialized data
is `Unknown`, a distinct third state that propagates through Kleene logic
and triggers faults when misused.  This eliminates an entire class of
initialization, use-after-free, and capability-confusion vulnerabilities
*by construction*.

### Design Pillars

1. **Balanced ternary** throughout — ISA, memory, registers, capabilities
2. **Formal verification** via Isabelle/HOL refinement proofs (seL4 methodology)
3. **Capability-based security** — grant/revoke with ternary access rights
4. **Performance** — < 5% overhead vs binary via 2-bit packed SIMD encoding
5. **Extensibility** — multi-radix hooks for AI/networking, Trithon interop
6. **Hardware alignment** — ISA targets 2026-2030 ternary silicon (Huawei CFET, Samsung CMOS-ternary, memristive in-memory compute)
7. **Ternary-First Bridge Protocol** — no internal binary regression; all binary/external-format interoperability is achieved through outward-facing bridges and converters (see §14A)

### Industry Alignment (2025-2026 Hardware Review)

seT5's ISA is designed to run on emerging ternary hardware:

| Vendor/Tech     | Key Development                                   | seT5 Alignment                          |
|-----------------|---------------------------------------------------|-----------------------------------------|
| **Huawei**      | CN119652311A patent (2025): balanced ternary AI    | Same encoding (-1/0/+1); carry-lookahead; variable operand lengths (1-3 trytes) |
| **Samsung/UNIST**| CMOS-compatible ternary (2017-2026): 45% area, 30% power reduction | Target for initial FPGA/ASIC prototypes |
| **Memristive**  | 1T1M TMR ternary gates: 95% power reduction for in-memory compute | Spill-to-memristive in register file; DOT_TRIT for inference |
| **Multi-radix** | Cisco G300 512-radix switches; radix-4 FFT in comms | FFT_STEP, RADIX_CONV instructions; G300-inspired load balancing |
| **RISC-V**      | Open ISA predicted as 2026 AI "dark horse" ($260B by 2030) | seT5 ISA extension model inspired by RISC-V custom instructions |

**Key metrics from industry:** 40-60% power reduction (Huawei), 36% fewer
interconnects (Samsung), 50% fewer transistors for add/sub (balanced ternary
symmetry).  seT5 targets these same efficiency gains.

---

## 2. Balanced Ternary ISA

### 2.1 Data Unit: the Tryte

The fundamental addressable unit is the **tryte**: a group of **6 trits**
(base case).  A 6-trit tryte encodes 3⁶ = **729 distinct states**, compared
to 256 for a binary byte.

```
Tryte layout (6 trits, MST first):

  ┌─────┬─────┬─────┬─────┬─────┬─────┐
  │ t₅  │ t₄  │ t₃  │ t₂  │ t₁  │ t₀  │   each tᵢ ∈ {-1, 0, +1}
  └─────┴─────┴─────┴─────┴─────┴─────┘

Value range (balanced): -364 … 0 … +364
  Formula: Σ tᵢ × 3ⁱ  for i = 0..5
```

**Variable tryte widths** are supported for specialized domains (aligned with
Huawei patent CN119652311A variable operand lengths 1-3 trytes):

| Width   | Trits | States | Use Case                               | Huawei Equiv.    |
|---------|-------|--------|----------------------------------------|------------------|
| Half    | 3     | 27     | Flags, small enums, opcode fields      | 1-tryte compact  |
| Base    | 6     | 729    | Standard addressing, register width    | 2-tryte standard |
| Double  | 12    | 531441 | Extended address space, large immediates| 3-tryte extended |
| Quad    | 24    | ~282B  | SIMD batch, cryptographic operations   | SIMD extension   |

**63% fewer digits** than binary for equivalent range — directly benefits
Trithon bigints and ML signed-weight representations.

### 2.2 Trit Encoding (Hardware / Emulation)

#### Scalar Encoding (`trit.h`)

`int8_t` with values `-1`, `0`, `+1`.  Clear, portable, used in all
host-side code and demos.

#### 2-Bit Packed Encoding (`trit_emu.h`)

| Value       | Binary | Hex  | Notes                                |
|-------------|--------|------|--------------------------------------|
| False (−1)  | `00`   | 0x0  | Lattice bottom                       |
| Unknown (0) | `01`   | 0x1  | Absorbs in AND; propagates           |
| True (+1)   | `11`   | 0x3  | Lattice top                          |
| Fault       | `10`   | 0x2  | Reserved — trap / hardware error     |

**Why T = 11 (not 10)?**
True encoded as `11` enables **bitwise Kleene AND** via `result = a & b`
on packed registers — no masking needed for the common case.
Kleene OR becomes `result = a | b`.  This yields **zero-overhead SIMD**
for 32-trit batches in 64-bit words.

#### Encoding Invariant

For any valid trit `t`, exactly one holds:

- `t == 0b00` (False)
- `t == 0b01` (Unknown)
- `t == 0b11` (True)

The pattern `0b10` is **never** valid; its presence signals a fault
(hardware error, uninitialized memory, or cosmic ray flip).

#### Isomorphism

`trit_pack` / `trit_unpack` in `trit.h` convert between scalar and packed
forms.  Both are semantically identical; packed is used for registers/SIMD.

### 2.3 Instruction Set — Postfix Notation

seT5 uses a **postfix (reverse Polish) instruction encoding**, matching the
two-stack execution model.  Instructions consume operands from the operand
stack and push results back.  This eliminates register-allocation complexity
in the code generator and maps naturally to the compiler's postfix IR
(`tools/compiler/src/postfix_ir.c`).

#### Core Instruction Categories

```
┌─────────────────────────────────────────────────────────────────┐
│                    seT5 ISA — Postfix Operations                │
├──────────────┬──────────────────────────────────────────────────┤
│ Category     │ Instructions                                    │
├──────────────┼──────────────────────────────────────────────────┤
│ Stack        │ PUSH, POP, DUP, SWAP, OVER, ROT                │
│ Arithmetic   │ ADD, SUB, MUL, DIV, MOD, NEG, INC              │
│ Logic        │ AND, OR, NOT, IMPLIES, EQUIV (Kleene K₃)       │
│ Comparison   │ EQ, NEQ, LT, GT, LEQ, GEQ                     │
│ Control      │ JMP, JZ, JNZ, CALL, RET, HALT                 │
│ Memory       │ LOAD, STORE, ALLOC, FREE                       │
│ Capability   │ CAP_GRANT, CAP_REVOKE, CAP_SEND, CAP_RECV     │
│ System       │ SYSCALL, TRAP, YIELD, NOP                      │
│ Multi-radix  │ RADIX_CONV, FFT_STEP, DOT_TRIT                │
└──────────────┴──────────────────────────────────────────────────┘
```

#### Minimal Logic Ops

Two foundational ternary logic gates handle all boolean decisions (matching
Huawei patent's inc/dec functions and Samsung's leakage-current third state):

- **Consensus (Kleene AND / meet):** `min(a, b)` — returns True only if
  both are True; Unknown if either is Unknown and neither is False.
  Implemented as `trit_consensus()` in `ternary.h`, `trit_and()` in `trit.h`.
- **Accept-Any (Kleene OR / join):** `max(a, b)` — returns True if either
  is True; Unknown if either is Unknown and neither is True.
  Implemented as `trit_accept_any()` in `ternary.h`, `trit_or()` in `trit.h`.

All other logic ops derive from these two plus NOT (involution: `-a`).
Formally verified in `proof/TritKleene.thy`.

**Symmetric negation** (trit flip: `-a`) is a single-gate operation in
balanced ternary — no sign bit to manipulate.  This is critical for:
- Trit Linux atomic ops (lock/unlock as +1/-1 flip)
- Ternary neural net inference (weight × activation = conditional negate)

#### Carry-Lookahead Ternary Arithmetic

Balanced ternary addition uses carry-lookahead to avoid ripple delays:

```
  Balanced ternary half-adder:
    sum   = (a + b + carry_in) mod 3     (balanced: result in {-1,0,+1})
    carry = (a + b + carry_in) div 3     (balanced division)

  Carry-lookahead for N-trit word:
    Generate: gᵢ = (aᵢ + bᵢ overflows)   → trit
    Propagate: pᵢ = (aᵢ + bᵢ == 0)       → trit
    Carry:    cᵢ₊₁ = gᵢ OR (pᵢ AND cᵢ)  (Kleene logic)
```

This gives O(log N) carry resolution vs O(N) for ripple-carry.
Directly implements Huawei patent's carry-lookahead arithmetic with
50% fewer transistors than binary equivalents.

#### Inc/Dec Operations

Per Huawei patent: dedicated `INC` and `DEC` instructions use N/P-type
transistor pairs for single-trit increment/decrement with carry:

```
  INC: -1 → 0 → +1 → -1 (wrap, carry_out = +1)
  DEC: +1 → 0 → -1 → +1 (wrap, borrow_out = -1)
```

Simple loops (counted by tryte) execute 3× fewer iterations than binary
for equivalent range — e.g., a 6-trit loop covers 729 vs 64 for 6 bits.

---

## 3. Two-Stack Execution Model (DSSP Heritage)

seT5's two-stack model descends directly from the **DSSP (Dialogue System
for Structured Programming)** designed by Brusentsov and Zhogolev for the
Setun-70 balanced ternary computer (1970).  DSSP separated data and control
flow using an operand stack and a return stack — the same architecture
Forth adopted.  seT5 restores this design to its native ternary substrate.

```
  ┌─────────────────┐     ┌──────────────────┐
  │  Operand Stack   │     │   Return Stack    │
  │  (data values)   │     │  (return addrs)   │
  │                  │     │                   │
  │  ┌───┐           │     │  ┌───┐            │
  │  │ +1│ ← TOS     │     │  │0x3│ ← TOS     │
  │  ├───┤           │     │  ├───┤            │
  │  │  0│           │     │  │0x1│            │
  │  ├───┤           │     │  ├───┤            │
  │  │ -1│           │     │  │0x0│            │
  │  └───┘           │     │  └───┘            │
  └─────────────────┘     └──────────────────┘
        │                         │
        │  PUSH/POP/DUP/SWAP     │  CALL/RET
        │  ADD/AND/OR/NOT        │
        │  LOAD/STORE            │
        ▼                         ▼
  ┌──────────────────────────────────────────┐
  │          Execution Engine (VM)            │
  │   Postfix dispatch: fetch → decode →     │
  │   pop operands → compute → push result   │
  └──────────────────────────────────────────┘
```

**Why two stacks?**

- **Security:** Return addresses are never exposed to data operations,
  preventing stack-smashing / ROP attacks.
- **Simplicity:** Postfix IR maps 1:1 to stack operations — the compiler
  (`tools/compiler/src/codegen.c`) emits instructions with no register
  allocation pass needed.
- **Verification:** Each stack has a simple invariant (bounded depth, typed
  elements) that is easy to prove in Isabelle/HOL.

### Stack Underflow / Overflow

- Underflow on operand stack returns `TRIT_UNKNOWN` (safe default).
- Overflow traps to the fault handler with a `TRIT2_FAULT` signal.
- Both conditions are detectable and configurable via capability rights.

---

## 4. Register File

seT5 provides **16 general-purpose trit registers** (R0–R15), each holding
one tryte (6 trits).  Four additional special registers handle control state:

```
  General Purpose:  R0  R1  R2  R3  R4  R5  R6  R7
                    R8  R9  R10 R11 R12 R13 R14 R15

  Special:
    PC   — Program Counter (12-trit double-tryte)
    SP   — Stack Pointer (operand stack)
    RSP  — Return Stack Pointer
    SR   — Status Register (flags: carry, overflow, unknown-propagated)
```

### Register Spilling

When register pressure exceeds 16, the compiler emits PUSH/POP sequences
to spill to the operand stack.  The spill cost is bounded: at most 2
instructions (PUSH old + POP new) per spill/fill, and the postfix model
naturally minimizes live values.

**Memristive spill target (future):** On hardware with 1T1M TMR ternary
SRAM, spills go to memristive in-memory compute cells instead of
stack — enabling 95% power reduction for register pressure scenarios
(per IEEE memristive ternary gate research).  The VM abstracts this
behind the same PUSH/POP interface.

### SIMD Registers (Extension)

For bulk operations, 4 **wide registers** (W0–W3) each hold a packed
`trit2_reg32` (32 trits in 64 bits), enabling SIMD Kleene AND/OR/NOT
on 32 trits per cycle via `trit_and_packed64()` / `trit_or_packed64()`.

### Zero-Trit Sparsity (N:M)

Registers track **zero-trit density** for dynamic sparsity optimization.
When a register contains >50% Unknown/zero trits, the hardware can skip
those positions in AND/OR operations (sparse execution).  This maps to
TENET-style N:M structured sparsity for ternary neural networks, where
zero-weights are naturally 0-trits — exploiting the third state for
free compression.

---

## 5. Memory Model

### 5.1 Tryte-Aligned Pages

Memory is organized in **tryte-aligned pages**.  The base page size is
**729 trits** (3⁶), chosen for natural ternary alignment.

```
  Physical Memory Layout:
  ┌─────────────────────────────────────────────────┐
  │ Page 0 (729 trits)  │ Page 1 (729 trits)  │ …  │
  ├─────────────────────┼─────────────────────┼─────┤
  │  Unknown-init       │  Unknown-init       │     │
  │  (all trits = 0)    │  (all trits = 0)    │     │
  └─────────────────────┴─────────────────────┴─────┘

  Virtual Address: 12-trit (double-tryte), maps 531441 trit locations
  Page Table Entry:
    ┌──────────┬──────────┬───────────┬──────────┐
    │ Frame #  │ Rights   │ Cached?   │ Valid    │
    │ (6 trit) │ (3 trit) │ (1 trit)  │ (1 trit) │
    └──────────┴──────────┴───────────┴──────────┘
    Rights: R/W/X as trits — Unknown = "not yet determined"
    Valid:  True = mapped, False = unmapped, Unknown = being swapped
```

### 5.2 Initialization Guarantee

**All freshly allocated pages are Unknown-initialized.**  This is the key
security property: no page ever contains stale data from another process.
When code attempts to branch on Unknown, the Kleene logic propagates it
(AND(T,U) = U), and `trit_to_bool_safe()` conservatively maps Unknown → False
(deny access).

### 5.3 Capability-Protected Access

Every memory access is mediated by a **capability** (see §6).  A capability
grants rights to a specific page frame.  Without a valid capability, memory
is inaccessible — there is no ambient authority.

---

## 6. Capability System

seT5 inherits seL4's capability model, extended with ternary access rights.

### 6.1 Capability Structure

```c
typedef struct {
    int object_id;    /* Target kernel object ID       */
    int rights;       /* Bitmask: R=1, W=2, G=4        */
    int badge;        /* IPC badge for endpoint discrim */
} seT5_cap;
```

Defined in `tools/compiler/include/set5.h`.

### 6.2 Kernel Object Types

| Object Type    | Enum               | Description                    |
|----------------|--------------------|---------------------------------|
| Endpoint       | `OBJ_ENDPOINT`     | Synchronous IPC channel        |
| Notification   | `OBJ_NOTIFICATION` | Asynchronous signal            |
| Thread         | `OBJ_THREAD`       | Thread control block           |
| Memory Frame   | `OBJ_MEMORY`       | Physical page frame            |
| CNode          | `OBJ_CNODE`        | Capability address space node  |

### 6.3 Cap Operations (Syscalls)

| Syscall          | Number | Description                                   |
|------------------|--------|-----------------------------------------------|
| `SYS_CAP_SEND`   | 4      | Send message via capability endpoint          |
| `SYS_CAP_RECV`   | 5      | Receive message from capability endpoint      |
| `SYS_CAP_GRANT`  | 6      | Grant cap with reduced rights (intersection)  |
| `SYS_CAP_REVOKE` | 7      | Revoke cap — zeros rights and badge           |

**Grant semantics:** `dest.rights = src.rights & requested_rights`.
Rights can only be **narrowed**, never widened — the monotonicity invariant.

**Ternary extension:** Capability rights can be `Unknown`, meaning
"not yet determined."  A capability with Unknown read-right **cannot** be
used for reading (conservative collapse: `trit_to_bool_safe(Unknown) = false`).
The capability must be explicitly promoted to True via a trusted grant.

### 6.4 Uncertainty Model — Markov Chain

Capability states evolve over time.  We model transitions as an absorbing
Markov chain over {F, U, T}:

```
        ┌ p_FF  p_FU  p_FT ┐
    P = │ p_UF  p_UU  p_UT │
        └ p_TF  p_TU  p_TT ┘

  Conservative security policy (unknown never spontaneously → true):

              ┌   1       0       0   ┐
    P_sec =   │   α     1−α      0   │
              └   0       β     1−β   ┘

  α = rate unknown resolves to false (timeout / revocation)
  β = rate true degrades to unknown (expiry / re-check)
```

**Key property:** π_U = 0 — no capability remains unknown forever.
Enforced by `trit_checked()` with fault flags at runtime.

---

## 7. Syscall Interface

The full syscall ABI is defined in `tools/compiler/include/set5.h`.
Calling convention: push args right-to-left, push syscall number, execute
`SYSCALL`.  Result is left on the operand stack.

```
  Syscall Dispatch:
  ┌──────────────────────────────────────────────────┐
  │         User Space                                │
  │   PUSH arg2                                       │
  │   PUSH arg1                                       │
  │   PUSH syscall_no                                 │
  │   SYSCALL ──────────────────────┐                 │
  └─────────────────────────────────│─────────────────┘
                                    │  trap
  ┌─────────────────────────────────▼─────────────────┐
  │         Kernel Space                               │
  │   syscall_dispatch(id, arg0, arg1)                 │
  │     ├─ SYS_EXIT (0)        → terminate             │
  │     ├─ SYS_WRITE (1)       → write to fd           │
  │     ├─ SYS_READ (2)        → read from fd          │
  │     ├─ SYS_MMAP (3)        → map memory page       │
  │     ├─ SYS_CAP_SEND (4)    → IPC send              │
  │     ├─ SYS_CAP_RECV (5)    → IPC receive            │
  │     ├─ SYS_CAP_GRANT (6)   → grant capability      │
  │     ├─ SYS_CAP_REVOKE (7)  → revoke capability     │
  │     ├─ SYS_THREAD_CREATE(8)→ create thread          │
  │     └─ SYS_THREAD_YIELD(9) → yield to scheduler    │
  └───────────────────────────────────────────────────┘
```

### Trit-Priority Scheduling

Thread priorities use **trit values** for a natural three-level scheme:

| Priority | Trit | Meaning                                   |
|----------|------|-------------------------------------------|
| Low      | -1   | Background / idle tasks                   |
| Normal   |  0   | Standard user threads                     |
| High     | +1   | Real-time / interrupt handlers            |

The scheduler selects the highest-priority runnable thread.  Priority
comparison uses balanced ternary ordering (−1 < 0 < +1), which is a
single trit comparison.  Equal priorities use round-robin.

`SYS_LOAD_BALANCE` (extended syscall) uses G300-inspired multi-radix
heuristics to distribute work across execution units.

---

## 8. IPC (Inter-Process Communication)

IPC follows the seL4 synchronous endpoint model:

```
  Thread A                    Endpoint (cap)              Thread B
  ────────                   ──────────────              ────────
  t_cap_send(ep, msg) ──►   ┌────────────┐   ◄── t_cap_recv(ep)
                             │  Badge: 42  │
                             │  Msg:  data │
                             └────────────┘
                             Synchronous rendezvous:
                             sender blocks until receiver ready
```

- **Synchronous endpoints** (`OBJ_ENDPOINT`): Sender blocks until receiver
  calls `t_cap_recv()`.  Zero-copy when possible.
- **Asynchronous notifications** (`OBJ_NOTIFICATION`): Non-blocking signal.
  Uses ternary semaphore: `{−1=empty, 0=pending, +1=signaled}`.
- **Badges** discriminate senders on a shared endpoint — the receiver sees
  which client sent the message without needing separate endpoints.

### IPC Payload

Messages carry a bounded number of trytes (configurable, default 6 trytes
= 36 trits).  Larger transfers use shared-memory pages with capability
delegation.

---

## 9. Multi-Radix Hooks (AI / Networking Extensions)

seT5 includes **instruction-level hooks** for mixed-radix computation,
targeting AI inference and signal processing.  These are informed by
2025-2026 industry trends: Cisco G300 512-radix AI switches (102.4Tb/s),
IEEE multi-radix FFT architectures, and ternary neural network research.

### 9.1 Radix-4 FFT Step

The `FFT_STEP` instruction performs a single butterfly operation in
radix-4 FFT, leveraging the fact that balanced ternary naturally maps
to the roots of unity for radix-3, and radix-4 composes with binary
twiddle factors.  Targets up to 4096-point transforms per IEEE
multi-radix FFT architectures for high-speed communications.

```
  FFT_STEP:
    pop  4 operands (trit-encoded complex values)
    butterfly multiply + accumulate
    push 4 results

  Performance: radix-4 reduces multiply count by 25% vs radix-2
  Use case: Trit Linux signal processing drivers, AI preprocessing
```

### 9.2 Dot Product (`DOT_TRIT`)

Ternary dot product for neural network inference where weights are
quantized to `{-1, 0, +1}`.  Directly targets Huawei's balanced-ternary
AI chip patent and ternary weight networks (TWN/TTQ):

```
  DOT_TRIT:
    Multiply-accumulate over trit vectors
    Weight × Activation: conditional negate/zero/pass
    No actual multiplication needed — O(N) adds only

  Zero-trit sparsity: skip 0-weight positions entirely
    → N:M structured sparsity (TENET-inspired)
    → 2-4x speedup for sparse ternary models
```

This is especially efficient for **ternary neural networks** (TWN/TTQ)
where the entire computation reduces to additions and sign flips.
With memristive in-memory compute, DOT_TRIT can execute directly in
the register spill target — computation and storage unified.

### 9.3 Radix Conversion (`RADIX_CONV`)

Converts between balanced ternary and other radix systems (binary,
radix-4, decimal) for interoperability with external systems.

```
  RADIX_CONV:
    pop radix_from, radix_to, value
    convert value from radix_from to radix_to
    push result

  Supported radixes: 2 (binary), 3 (balanced ternary),
    4 (radix-4/quaternary), 10 (decimal)
```

Critical for Trit Linux compatibility (binary↔ternary syscall translation)
and Trithon (Python int↔trit conversion for NumPy interop).

### 9.4 Load-Balance Telemetry (`TRIT_LB`)

Inspired by Cisco G300 high-radix AI networking switches:

```
  TRIT_LB:
    pop  priority(-1/0/+1), affinity(-1/0/+1), load_metric
    compute optimal placement across execution units
    push target_unit_id

  Use case: Trit Linux scheduler distributes threads across
    ternary processing elements using trit-priority ordering.
    G300-style telemetry enables adaptive load balancing for
    AI inference workloads at 102.4Tb/s network scale.
```

---

## 10. TBE — Ternary Bootstrap Environment

The **TBE** (`src/tbe_main.c`) is seT5's minimal userspace shell — the
first program that runs after kernel boot.  It provides a 15-command
interactive environment for I/O, environment management, syscall testing,
Kleene logic operations, and Trithon interop.

### 10.1 Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                        TBE Shell                            │
│  ┌────────────┐  ┌────────────┐  ┌────────────────────┐    │
│  │ Env Vars   │  │ Trit Ops   │  │  Trithon Interop   │    │
│  │ (key→trit) │  │ inc/dec    │  │  (expr evaluator)  │    │
│  │ 16 slots   │  │ consensus  │  │  T&F, ~U, etc.     │    │
│  │ BT encoded │  │ accept_any │  │                    │    │
│  └────────────┘  └────────────┘  └────────────────────┘    │
│  ┌────────────┐  ┌────────────┐  ┌────────────────────┐    │
│  │ Syscall    │  │ Multi-Radix│  │  WCET Telemetry    │    │
│  │ dispatch   │  │ dot / fft  │  │  6 probes, budget  │    │
│  │ + fallback │  │ regs 0-15  │  │  violation detect  │    │
│  └────────────┘  └────────────┘  └────────────────────┘    │
├─────────────────────────────────────────────────────────────┤
│                kernel_state_t (seT5 microkernel)            │
│   mem · ipc · sched · mr · caps[64] · stacks               │
└─────────────────────────────────────────────────────────────┘
```

### 10.2 Commands (15)

| Command       | Description                                  | Subsystem       |
|---------------|----------------------------------------------|-----------------|
| `help`        | Print command list                           | Shell           |
| `echo`        | Echo text to stdout                          | Shell           |
| `env`         | Print trit-encoded environment variables     | Env             |
| `setenv`      | Set env var (int → balanced ternary)         | Env             |
| `reg`         | Display 32-trit register                     | Multi-radix     |
| `dot`         | Dot product of two registers                 | Multi-radix     |
| `syscall`     | Direct kernel syscall dispatch               | Syscall         |
| `trit_inc`    | Balanced ternary increment                   | Trit ops        |
| `trit_dec`    | Balanced ternary decrement                   | Trit ops        |
| `consensus`   | Kleene AND of two registers                  | Trit ops        |
| `accept_any`  | Kleene OR of two registers                   | Trit ops        |
| `fft`         | Radix-3 FFT butterfly step                   | Multi-radix     |
| `wcet`        | Print WCET probe telemetry                   | WCET            |
| `trithon`     | Evaluate Trithon trit expression             | Interop         |
| `exit`        | Shutdown TBE                                 | Shell           |

### 10.3 Environment Variables

Environment variables store values as **balanced ternary trit arrays**
using Avizienis encoding (the standard balanced representation).  Each
env entry has a 3-state `validity` flag:

- **T** = active — normal use
- **U** = shadow — temporarily suspended (future: copy-on-write)
- **F** = deleted — slot available for reuse

### 10.4 Syscall Fallback

When a syscall fails (negative `retval`), TBE logs the failure to stderr
and emulates a safe result (`retval=0`, `result_trit=Unknown`).  This
ensures the shell remains operational even during kernel development or
hardware bring-up.

### 10.5 Design Rationale

TBE serves the same role as a BIOS/UEFI shell or seL4's `sel4test`:

1. **Validate kernel primitives** — every syscall is testable interactively
2. **Bootstrap Trithon** — the Trithon evaluator hook provides a path
   from shell to Python (CFFI, future)
3. **Hardware bring-up** — register display and trit inc/dec verify
   the ALU on new ternary silicon
4. **Self-documenting** — `help` + `wcet` give immediate observability

---

## 11. Layer Stack

```
┌──────────────────────────────────────────────────────────────┐
│  Trithon / Python Interop  (trithon/trithon.py)             │
├──────────────────────────────────────────────────────────────┤
│  Trit Linux Compatibility  (include/set5/posix.h)           │
├──────────────────────────────────────────────────────────────┤
│  TBE Bootstrap Shell  (src/tbe_main.c — 15 commands)        │
├──────────────────────────────────────────────────────────────┤
│  seL4 Kernel Object Model  (include/set5/sel4_ternary.h)    │
│    CNode · TCB · Endpoint · Notification · VSpace ·         │
│    IRQHandler · IRQControl · Reply · SchedContext ·          │
│    SchedControl · Untyped — plus POSIX translation          │
├──────────────────────────────────────────────────────────────┤
│  Kernel Modules  (src/init.c, memory, IPC, scheduler)       │
├──────────────────────────────────────────────────────────────┤
│  Syscall ABI     (include/set5/syscall.h — 14 syscalls)     │
├──────────────────────────────────────────────────────────────┤
│  Multi-Radix     (include/set5/multiradix.h)                │
│    DOT_TRIT · FFT_STEP · RADIX_CONV · load balance          │
├──────────────────────────────────────────────────────────────┤
│  WCET / Telemetry (include/set5/wcet.h, qemu_trit.h)       │
├──────────────────────────────────────────────────────────────┤
│  Device Driver    (include/set5/dev_trit.h — /dev/trit)     │
├──────────────────────────────────────────────────────────────┤
│  Ternary Compiler  (tools/compiler/ — submodule)            │
│    Parser → Postfix IR → Codegen → VM / Verilog             │
├──────────────────────────────────────────────────────────────┤
│  Application / Demo  (demo/*.c)                             │
├──────────────────────────────────────────────────────────────┤
│  Type System  (trit_type.h)       ← trit_checked(), faults  │
├──────────────────────────────────────────────────────────────┤
│  Casting      (trit_cast.h)       ← embed/project K₃↔Bool   │
├──────────────────────────────────────────────────────────────┤
│  Core Logic   (trit.h)            ← Kleene AND/OR/NOT, SIMD │
├──────────────────────────────────────────────────────────────┤
│  Emulation    (trit_emu.h)        ← 2-bit packed, bulk ops  │
├──────────────────────────────────────────────────────────────┤
│  Formal Proofs (proof/*.thy)      ← Isabelle/HOL, AFP reuse │
├──────────────────────────────────────────────────────────────┤
│  Clang Extensions (clang/lib/*)   ← Sema, pragma, codegen   │
├──────────────────────────────────────────────────────────────┤
│  Hardware      (tools/compiler/hw/) ← Verilog ALU, FPGA     │
└──────────────────────────────────────────────────────────────┘
```

---

## 12. Verification Chain

Following seL4's refinement proof architecture, extended for ternary:

```
Abstract Model (HOL)  ──refines──►  Executable Spec (C)  ──validates──►  Binary
      │                                    │                                │
      ▼                                    ▼                                ▼
  TritKleene.thy              trit.h / trit_emu.h              gcc -O2 output
  TritOps.thy                 trit_cast.h                      VM bytecode
  CapSafety.thy               set5.h (syscall ABI)             Verilog netlist
  IPCCorrect.thy              src/init.c (kernel)
  MemIsolation.thy            src/memory.c
  SecurityCIA.thy             src/security.c
  TranslationValidation.thy   tools/compiler/
  TJSON_Validation.thy        include/set5/
```

### Proof Obligations — All 8 Theories Verified

| Property              | Theory File           | Status    | Time  |
|-----------------------|-----------------------|-----------|-------|
| Kleene lattice laws   | `TritKleene.thy`      | Proven    | 0.8s  |
| Ternary arithmetic    | `TritOps.thy`         | Proven    | 0.9s  |
| Capability safety     | `CapSafety.thy`       | Proven    | 0.1s  |
| Memory isolation      | `MemIsolation.thy`    | Proven    | 0.3s  |
| IPC correctness       | `IPCCorrect.thy`      | Proven    | 1.1s  |
| CIA security          | `SecurityCIA.thy`     | Proven    | 2.9s  |
| Translation validation| `TranslationValidation.thy`| Proven | 3.9s  |
| JSON validation       | `TJSON_Validation.thy`| Proven    | 0.6s  |

**Total proof time: 11.3 seconds across all 8 theories.**

### Isabelle Tooling

Isabelle2025-2 is installed at `/opt/isabelle/Isabelle2025-2/` with a symlink
at the repo root (`Isabelle2025-2/`, gitignored). A wrapper script at
`tools/isabelle` provides a consistent entry point:

```bash
tools/isabelle build -d proof seT6_Proofs   # Build all 8 theories
tools/isabelle jedit -d proof -l HOL         # Interactive proof IDE
```

> **Note:** The symlink may not persist across Codespaces sessions. If
> `Isabelle2025-2/bin/isabelle` fails, recreate it:
> `ln -sfn /opt/isabelle/Isabelle2025-2 Isabelle2025-2`

For the complete proof development workflow, see
[TESTS_AND_PROOFS_INSTRUCTIONS.md](TESTS_AND_PROOFS_INSTRUCTIONS.md).

### Comprehensive Test Coverage

seT5 achieves complete verification through multiple complementary approaches:

- **Formal Proofs**: 8 Isabelle/HOL theories providing mathematical guarantees
- **Unit Tests**: 228 compiler tests validating individual components
- **Integration Tests**: 560 kernel tests verifying cross-module interactions
- **System Tests**: 99 Trithon assertions confirming end-to-end functionality
- **Performance Benchmarks**: TernBench quantifying efficiency gains
- **Hardware Validation**: 505 additional tests for chip compatibility

**Total: 5371+ runtime assertions across 35 test suites, all passing with 0 failures.**

This multi-layered verification strategy ensures seT5 delivers on its promise
of a zero-vulnerability ternary microkernel, with every security property
validated through both formal mathematics and empirical testing.

---

## 13. Extensions Roadmap

### 13.1 Trithon — Python Interop

A Python-to-ternary bridge enabling:

- `import trithon` — access trit types as native Python objects
- NumPy-compatible ternary arrays for AI workloads
- CFFI bindings to `trit_emu.h` for SIMD bulk ops from Python
- Jupyter notebook integration for interactive ternary computing

### 13.2 Trit Linux

A Linux compatibility layer running atop the seT5 microkernel:

- POSIX syscall translation: binary syscalls map to ternary via
  `trit_from_bool()` / `trit_to_bool_safe()`
- `/dev/trit` device for user-space access to ternary registers
- `LD_PRELOAD`-style shim for binary executables on ternary pages

### 13.3 Hardware Targets

- **FPGA:** Verilog ALU in `tools/compiler/hw/ternary_alu.v`; synthesis
  targets iCE40 (Lattice) and Artix-7 (Xilinx) via constraint files
  (`fpga_constraints.pcf`, `fpga_constraints.xdc`)
- **Huawei CFET (2026-2030):** Balanced ternary AI chip per patent
  CN119652311A; EUV-alternative 2nm fab, scaling to 1nm CFET.
  seT5 ISA is directly compatible with patent's gate-level design.
- **Samsung CMOS-ternary:** UNIST leakage-current third state;
  45% area reduction, 30% power savings.
- **Memristive 1T1M:** TMR-based ternary gates for in-memory compute;
  95% power reduction for DOT_TRIT and capability batch checks.
- **CNTFET:** Carbon nanotube FET ternary gates (research, post-2026)

---

## 14. Performance Gate

| Metric                 | Target    | Rationale                                      |
|------------------------|-----------|-------------------------------------------------|
| 1M Kleene AND time     | < 0.002 s | Matches INITIAL_PROJECT_ANSWERS estimate        |
| Overhead vs binary AND | **< 5%**  | T=11 eliminates masking; 4x unroll amortizes    |
| WCET impact            | < 10%     | seL4: "security is no excuse for poor perf"     |
| IPC round-trip         | < 1 µs    | seL4 benchmark baseline for synchronous IPC     |
| Syscall overhead       | < 500 ns  | Comparable to seL4 fastpath                     |

---

## 14A. Ternary-First Bridge Protocol (MANDATORY)

> **Effective 2026-02-20 — applies to all seT6 full-stack components.**

When any aspect of seT6 — kernel, compiler, HALs, networking, storage,
AI acceleration, Trithon, Trit Linux, or any future module — encounters
a situation requiring interaction with binary or other non-ternary formats,
the following protocol is **mandatory and immutable**:

1. **No internal binary regression.** seT6 internals operate exclusively
   in balanced ternary ({-1, 0, +1}) and multi-radix representations.
   Binary must never be used as an internal data path, logic primitive,
   or storage format within any seT6 component.

2. **Build bridges outward.** Where interoperability with binary systems,
   protocols, or hardware is required, seT6 provides dedicated
   **bridge modules** and **format converters** at the system boundary.
   These bridges translate ternary ↔ binary (or ternary ↔ other radix)
   at the edge, preserving ternary purity inside.

3. **Native hybrid interoperability.** Bridge modules provide
   first-class, tested, verified interoperability — not second-class
   compatibility shims. They increase the value of seT6 for all users
   by enabling seamless integration with the existing binary ecosystem
   while maintaining ternary-first internals.

4. **Direction of expansion.** We build **outwards** from ternary to
   binary, never inwards from binary to ternary. The conversion
   direction is always:
   ```
   seT6 ternary core  ──▶  bridge/converter  ──▶  binary world
   ```
   The binary world reaches seT6 through the same bridges:
   ```
   binary world  ──▶  bridge/converter  ──▶  seT6 ternary core
   ```

5. **Multi-radix to binary, outwards.** For multi-radix components
   (PAM-3, radix-4 FFT, mixed-radix AI), the same principle applies:
   convert outward to binary only at the interface boundary.

**Examples of compliant bridge modules:**
- `src/pam3_transcode.c` — PAM-3 ternary ↔ PAM-4 binary SerDes
- `src/intel_pam3_decoder.c` — Intel PAM-3 ↔ binary Ethernet
- `trit_linux/` — POSIX binary syscall ↔ ternary kernel translation
- `trithon/` — Python binary objects ↔ ternary C extension types
- `trit_from_bool()` / `trit_to_bool_safe()` — scalar conversion primitives
- `RADIX_CONV` instruction — general multi-radix ↔ ternary conversion

**Violations of this protocol are treated as regressions and will be
reverted by Crown Jewel reversion guards.** See `CROWN_JEWELS.md`.

---

## 15. Swarm Roles

| Role           | Agent Type  | Responsibility                                               |
|----------------|-------------|--------------------------------------------------------------|
| **Architect**  | Lead (Opus) | Decompose specs into micro-tasks; maintain TODOLIST.md        |
| **Synthesizer**| Coder       | Generate C headers, LLVM IR stubs, Clang patches              |
| **Prover**     | Verifier    | Run Isabelle/HOL; discharge lemmas; generate TritOps.thy      |
| **Optimizer**  | Perf agent  | Profile SIMD paths; enforce <5% gate; tune bulk ops           |
| **Librarian**  | RAG agent   | Query AFP, seL4 docs, Setun papers for context                |

---

## 16. References

### Foundational
- seL4 Whitepaper (Heiser, 2025) — verification chain, capability model
- AFP "Three-Valued Logic" — Kleene lattice formalization
- AFP "Kleene Algebra with Tests" — program logic adaptation
- Brusentsov (1958) — Setun balanced ternary computer
- Brusentsov & Zhogolev (1970, 1979) — DSSP/Setun-70 two-stack architecture;
  seT5's operand+return stack model is a direct descendant
- Connelly (1958) — Ternary computing with balanced logic
- Knuth, *TAOCP Vol. 2* §4.1 — balanced ternary arithmetic, efficiency analysis

### Hardware (2025-2026)
- **Huawei CN119652311A** (filed 2023, pub. 2025) — ternary logic gate circuit, AI chip, carry-lookahead, variable operand lengths
- **Samsung/UNIST** (2017-2019) — CMOS-compatible ternary semiconductor via leakage current third state
- IEEE memristive ternary gates (2025) — 1T1M TMR OR/inverter, 95% power reduction for in-memory compute
- Multi-radix FFT architectures (IEEE 2025) — radix-4/hybrid up to 4096 points
- Cisco G300 (2026) — 512-radix AI networking switch, 102.4Tb/s, multi-radix telemetry
- TrendForce (2026) — Huawei EUV-alternative 2nm ternary fab roadmap

### AI / Efficiency
- Li et al. (2016) — Ternary Weight Networks (TWN) for neural inference
- Zhu et al. (2020) — TENET: N:M structured sparsity for ternary neural networks
- Blackham et al. (2011) — WCET analysis for protected OS kernels
- Jones (2015) — Ternary efficiency: 62% more logic gates, 36% fewer interconnects

### Architecture
- G300 architecture — multi-radix scheduling heuristics
- RISC-V ISA (2024) — custom instruction extension model
- NeuroBench (2025) — neuromorphic / non-binary edge benchmarks
