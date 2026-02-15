# Huawei CN119652311A Ternary Chip — seT5 Integration Guide

## Patent Reference

| Field       | Value                                              |
|-------------|----------------------------------------------------|
| Patent ID   | CN119652311A                                       |
| Title       | Ternary Logic Gate Circuit, Computing Circuit, Chip, and Electronic Device |
| Assignee    | Huawei Technologies Co., Ltd.                      |
| Filed       | 2023-09-18                                         |
| Published   | 2025-03-18                                         |
| PCT         | PCT/CN2024/119205                                  |
| IPC Class   | G06F7/49 (Ternary radix computation)               |

## Architecture Overview

The Huawei CN119652311A chip implements ternary logic and arithmetic using
Carbon Nanotube Field-Effect Transistors (CNTFETs) with three threshold
voltage classes:

| Class | Name | Range       | Role               |
|-------|------|-------------|---------------------|
| LVT   | Low  | 0.20–0.30 V | Fast switching     |
| MVT   | Mid  | ~0.40 V     | Intermediate       |
| HVT   | High | 0.60–0.70 V | Voltage separation |

**Constraint:** LVT + HVT < VDD (ensures correct three-level discrimination)

### Logic Values

| Huawei | Voltage | seT5 Balanced | Symbolic      |
|--------|---------|---------------|---------------|
| 0      | VGND    | −1            | TRIT_FALSE    |
| 1      | VDD/2   | 0             | TRIT_UNKNOWN  |
| 2      | VDD     | +1            | TRIT_TRUE     |

**Translation:** `huawei_val = balanced + 1` / `balanced = huawei_val - 1`

### Fundamental Gates

| Gate | Function | Truth Table         | Transistors | Description              |
|------|----------|---------------------|-------------|--------------------------|
| INC  | f5       | {0→1, 1→2, 2→0}    | 9 (7+2 NTI) | Self-incrementing        |
| DEC  | f19      | {0→2, 1→0, 2→1}    | 9 (7+2 PTI) | Self-decrementing        |
| NTI  | f18      | {0→2, 1→0, 2→0}    | 2           | Negative ternary inverter|
| PTI  | f24      | {0→2, 1→2, 2→0}    | 2           | Positive ternary inverter|
| PB   | f8       | {0→0, 1→2, 2→2}    | 2           | Positive buffer          |
| NB   | f2       | {0→0, 1→0, 2→2}    | 2           | Negative buffer          |

INC and DEC compose **all 27 single-variable ternary functions**.

### Computing Circuits

| Circuit | Patent Fig. | Inputs | Outputs       | Description                      |
|---------|-------------|--------|---------------|----------------------------------|
| Tsum    | Fig. 5      | A, B   | S             | Ternary sum (A+B) mod 3          |
| THA     | Fig. 6      | A, B   | Sum, Carry    | Ternary half-adder               |
| TFA     | Fig. 7      | A,B,C  | Sum, Carry    | Ternary full-adder (2-stage THA) |
| TMul    | —           | A, B   | Prod, Carry   | Exact 1-trit multiplier          |
| ATMul   | —           | A, B   | Prod, (Carry≈)| Approximate multiplier           |
| Mul2×2  | Fig. 11b    | A[2], B[2] | P[4]      | 2-trit × 2-trit multiply         |
| Mul6×6  | Fig. 14     | A[6], B[6] | P[12]     | 6-trit × 6-trit multiply         |

## File Map

All files are **new additions** — no existing seT5 code was modified.

### Headers (include/set5/)

| File                      | Purpose                                        |
|---------------------------|-------------------------------------------------|
| `huawei_cn119652311a.h`   | Top-level header: types, value translation, gate functions, chip caps, HAL state |
| `huawei_mmio.h`           | Full MMIO register map (4 KB aperture)          |
| `huawei_alu.h`            | ALU operation interface (Tsum, THA, TFA, TMul, ATMul, wide multiply, word add, dot product, FFT butterfly) |

### Implementation (src/)

| File             | Purpose                                                  |
|------------------|----------------------------------------------------------|
| `huawei_hal.c`   | HAL init/shutdown, silicon detection, capability probing  |
| `huawei_alu.c`   | Dual-path ALU (MMIO hardware dispatch + software emulation) |

### Hardware (hw/)

| File                          | Purpose                                    |
|-------------------------------|--------------------------------------------|
| `huawei_cn119652311a.dts`     | Device tree source for platform discovery  |
| `huawei_cn119652311a_alu.v`   | Verilog simulation model of the full ALU   |

### Tests (tests/)

| File                             | Purpose                                |
|----------------------------------|----------------------------------------|
| `test_huawei_cn119652311a.c`     | Comprehensive test suite (50+ tests)   |

## Building

### Test Suite

```bash
gcc -Wall -Wextra -Iinclude -o test_huawei_cn119652311a \
    tests/test_huawei_cn119652311a.c \
    src/huawei_alu.c src/huawei_hal.c
./test_huawei_cn119652311a
```

Or via the Makefile:

```bash
make test_huawei_cn119652311a
./test_huawei_cn119652311a
```

### Verilog Simulation

The Verilog model can be simulated with Icarus Verilog or any compatible tool:

```bash
iverilog -o huawei_alu_sim hw/huawei_cn119652311a_alu.v
vvp huawei_alu_sim
```

## API Usage

### Initialization

```c
#include "set5/huawei_cn119652311a.h"
#include "set5/huawei_alu.h"

hw_hal_state_t hal;
hw_hal_init(&hal);   /* Auto-detects hardware or falls back to emulation */

/* Check mode */
if (hw_hal_mode(&hal) == HW_MODE_EMULATED)
    printf("Running in emulation mode\n");
```

### Value Translation

```c
trit balanced = TRIT_TRUE;           /* +1 */
hw_trit hw = hw_from_balanced(balanced); /* 2 */
trit back = hw_to_balanced(hw);      /* +1 */
```

### Single-Trit Operations

```c
trit result;

/* INC gate: -1→0, 0→+1, +1→-1 */
result = hw_alu_inc(&hal, TRIT_UNKNOWN);  /* 0 → +1 */

/* DEC gate: -1→+1, 0→-1, +1→0 */
result = hw_alu_dec(&hal, TRIT_TRUE);     /* +1 → 0 */

/* Ternary sum: (A + B) mod 3 */
result = hw_alu_tsum(&hal, TRIT_TRUE, TRIT_TRUE);  /* +1+1 ≡ -1 (mod 3) */
```

### Arithmetic with Carry

```c
/* Half-adder */
hw_half_adder_result_t ha = hw_alu_half_add(&hal, TRIT_TRUE, TRIT_TRUE);
/* ha.sum = -1, ha.carry = +1  (since +1 + +1 = +2 = +1*3 + (-1)) */

/* Full-adder */
hw_full_adder_result_t fa = hw_alu_full_add(&hal, +1, +1, +1);
/* fa.sum = 0, fa.carry = +1  (since +1 + +1 + +1 = +3 = +1*3 + 0) */
```

### Multiplication

```c
/* 1-trit exact multiply */
trit p = hw_alu_mul1(&hal, TRIT_TRUE, TRIT_FALSE);  /* +1 * -1 = -1 */

/* 2-trit × 2-trit (exact) */
hw_mul_result_t r = hw_alu_mul2x2(&hal, 3, 4, HW_COMP_NONE);
/* r.result = 12 */

/* 2-trit × 2-trit (approximate with +9 compensation) */
hw_mul_result_t ra = hw_alu_mul2x2(&hal, 4, 4, HW_COMP_PLUS9);
/* r.result ≈ 16, with reduced error from compensation */

/* 6-trit × 6-trit */
hw_mul_result_t r6 = hw_alu_mul6x6(&hal, 100, 100, HW_COMP_NONE);
/* r6.result = 10000 */
```

### Word Operations

```c
/* Add two 6-trit words */
trit a[] = { +1, +1, +1, 0, 0, 0 };  /* = 1 + 3 + 9 = 13 */
trit b[] = { -1, +1, 0, 0, 0, 0 };   /* = -1 + 3 = 2 */
trit result[6];
trit carry = hw_alu_add_word(&hal, a, b, result, 6);

/* Dot product */
int dp = hw_alu_dot_product(&hal, a, b, 6);

/* FFT butterfly */
trit out0, out1, out2;
hw_alu_fft_butterfly(&hal, in0, in1, in2, &out0, &out1, &out2);
```

### Shutdown

```c
hw_hal_shutdown(&hal);
```

## Approximate Multiplication

The patent's key innovation for AI/ML workloads: the **approximate multiplier
(ATMul)** ignores the carry when both inputs equal 2 (balanced: +1×+1).

| Mode           | Behaviour                           | Use Case       |
|----------------|-------------------------------------|----------------|
| `HW_COMP_NONE` | Raw approximation (max error)       | Lowest power   |
| `HW_COMP_PLUS6`| Adds 6 to partial product (P1 += 2) | Medium accuracy|
| `HW_COMP_PLUS9`| Adds 9 to partial product (P2 += 1) | Best accuracy  |

For exact computation (e.g., cryptographic or kernel operations), use the
TMul-based path or pass `HW_COMP_NONE` with single-trit operands (which are
always exact).

## Integration with Existing seT5 Subsystems

### multiradix.h

The `hw_alu_dot_product()` and `hw_alu_fft_butterfly()` functions map directly
to the `DOT_TRIT` and `FFT_STEP` operations in multiradix.h.  When the Huawei
chip is present, these accelerate the multiradix register-file operations
using native hardware chains of full-adders and summing circuits.

### dev_trit.h

The existing `/dev/trit` ioctl interface can be extended (without modifying
the existing header) to support Huawei-specific opcodes by adding a new
ioctl command range in a supplementary driver module.

### trit_emu.h

The `trit2` packed encoding (2-bit per trit) is compatible with the MMIO
register format.  The functions `hw_from_trit2()` and `hw_to_trit2()` handle
conversion between seT5's packed format and the Huawei encoding.

### Emulated vs. Hardware Mode

All ALU functions check `hal.mode` at runtime:

1. **MMIO mode** (`HW_MODE_MMIO`): Writes operands to MMIO registers, issues
   the command, polls for completion, reads the result.
2. **Emulated mode** (`HW_MODE_EMULATED`): Executes the same logic in software,
   matching the patent's circuit behaviour exactly.
3. **Simulated mode** (`HW_MODE_SIMULATED`): Reserved for Verilog co-simulation.

The HAL automatically selects the mode during `hw_hal_init()` based on
silicon detection.

## Verilog Model

The file `hw/huawei_cn119652311a_alu.v` provides a synthesizable simulation
model of the entire ALU with:

- All 6 gate primitives (NTI, PTI, PB, NB, INC, DEC)
- Summing circuit (Tsum) with NTI/PTI signal processing
- Carry device with PB/NB AND logic
- Half-adder (THA) and full-adder (TFA)
- Exact (TMul) and approximate (ATMul) multipliers
- Compensation units (+6. +9)
- 2×2 and 6×6 multiplier circuits
- Parameterized multi-trit word adder
- Top-level ALU with MMIO register interface

The register addresses in the Verilog model match `huawei_mmio.h` exactly,
enabling co-simulation with the C software stack.

## Device Tree

The file `hw/huawei_cn119652311a.dts` provides a device tree fragment that
describes the ternary ALU IP block:

```dts
ternary_alu@40100000 {
    compatible = "huawei,cn119652311a-ternary-alu";
    reg = <0x40100000 0x1000>;
    /* ... voltage, feature, transistor parameters ... */
};
```

Include this in the board-level device tree for any SoC integrating the
Huawei ternary ALU IP.
