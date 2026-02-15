# Samsung US11170290B2 NAND Inference Engine — seT6 Integration Guide

## Patent Reference

| Field             | Value                                                             |
|-------------------|-------------------------------------------------------------------|
| Patent ID         | US11170290B2                                                     |
| Title             | Realization of Neural Networks with Ternary Inputs and Binary Weights in NAND Memory Arrays |
| Original Assignee | SanDisk Technologies LLC                                         |
| Current Assignee  | Samsung Electronics Co., Ltd.                                    |
| Filed             | 2019-03-28                                                       |
| Granted           | 2021-11-09                                                       |
| IPC Class         | G06F7/5443 (Sum of products)                                     |
| Inventors         | Tung Thanh Hoang, Won Ho Choi, Martin Lueker-Boden               |

## Architecture Overview

The Samsung US11170290B2 chip implements **in-memory neural network inference**
using NAND flash arrays.  Rather than transferring weights to a separate MAC
unit, the multiply-accumulate is performed **within the memory array itself**,
eliminating the memory ↔ compute bottleneck.

### Core Concept: Unit Synapse

A **unit synapse** is a pair of series-connected SLC (single-level cell) NAND
memory cells on a common NAND string.  Each pair stores one binary weight:

| Weight | FG1 (First Cell) | FG2 (Second Cell) |
|--------|-------------------|-------------------|
| +1     | Erased ("1")      | Programmed ("0")  |
| −1     | Programmed ("0")  | Erased ("1")      |

### Voltage Levels

| Level | Name   | Description                                        |
|-------|--------|----------------------------------------------------|
| Vread | Low    | Distinguishes erased from programmed cells          |
| Vpass | High   | Causes any cell to conduct regardless of state      |

- At **Vread**: only erased cells (low Vth, "1" state) conduct
- At **Vpass**: all cells (erased and programmed) conduct

### Input Encoding

Ternary inputs {−1, 0, +1} are encoded as voltage patterns on word-line pairs:

| Input | V1 (WL1) | V2 (WL2) | Meaning                         |
|-------|----------|----------|----------------------------------|
| −1    | Vpass    | Vread    | FG1 always conducts              |
| +1    | Vread    | Vpass    | FG2 always conducts              |
|  0    | Vread    | Vread    | Only erased cells conduct (ZID)  |

### XNOR Output

When input and weight **match** → the NAND string **conducts** (logic +1).
When they **differ** → the string **does not conduct** (logic −1).

For zero input → the string never conducts (always reads as −1), but the
output is excluded from the counter by the Zero Input Detection (ZID) circuit.

### All Six Cases (Patent FIGS 12-15)

| Case | Weight | Input | FG1→V1 | FG2→V2 | Conducts? | XNOR |
|------|--------|-------|--------|--------|-----------|------|
| 1    | +1     | +1    | E@Vread=✓ | P@Vpass=✓ | **Yes** | +1 |
| 2    | +1     | −1    | E@Vpass=✓ | P@Vread=✗ | **No**  | −1 |
| 3    | −1     | +1    | P@Vread=✗ | E@Vpass=✓ | **No**  | −1 |
| 4    | −1     | −1    | P@Vpass=✓ | E@Vread=✓ | **Yes** | +1 |
| 5    | +1     |  0    | E@Vread=✓ | P@Vread=✗ | **No**  | (excluded by ZID) |
| 6    | −1     |  0    | P@Vread=✗ | E@Vread=✓ | **No**  | (excluded by ZID) |

## Dot-Product Computation

### BNN (Binary Neural Network) — Equation 1

$$P_{bnn} = 2 \cdot CNT_{out} - S$$

Where:
- $CNT_{out}$ = count of conducting NAND strings (XNOR matches)
- $S$ = input vector dimension (total number of synapses)

### TBN (Ternary-Binary Network) — Equation 2

$$P_{tbn} = 2 \cdot CNT_{out} - S_{tbn}$$
$$S_{tbn} = S - Z$$

Where:
- $Z$ = number of zero inputs (detected by ZID circuit)
- $CNT_{out}$ excludes sense amplifier outputs for zero-input positions

### Zero Input Detection (ZID) Circuit

The ZID circuit (FIG 22) consists of:

1. **NOR logic blocks (2203)**: one per word-line pair. Computes:
   `is_zero[i] = NOR(V1[i] − Vread, V2[i] − Vread)`
   When both word lines are at Vread → zero input detected.

2. **Combinational logic (CL 2205)**: generates the **Block Counter Control
   (BCC)** signal, which tells the counter circuit to skip the current
   synapse position.

3. **ZID_Enb**: mode register bit that enables/disables ZID.
   - Enabled in TBN mode (ternary inputs possible)
   - Disabled in BNN mode (no zero inputs)

## Parallelism Hierarchy

| Level | Patent Fig | Description | Throughput Gain |
|-------|-----------|-------------|-----------------|
| Sequential | — | One synapse sensed per cycle per bit line | Baseline |
| Multi-block | FIG 27 | Multi-bit SA senses multiple blocks concurrently | ×N blocks |
| Multi-plane | FIG 29 | Same weights on different planes, different inputs | ×M planes |
| Pipelining | FIG 30 | Different DNN layers mapped to different planes | Latency hiding |

### Multi-Block (FIG 27)
- Multiple blocks within the same plane store weights for different output neurons
- A **multi-bit sense amplifier** senses one bit from each block per cycle
- Counter/summation circuits (CSC) maintain separate accumulators per block

### Multi-Plane (FIG 29)
- The same weight matrix is stored in corresponding blocks of multiple planes
- Different input vectors are applied to each plane
- All planes compute dot-products simultaneously

### Plane Pipelining (FIG 30)
- Different DNN layers are stored in different planes
- Layer 0 output → activation → Layer 1 input → ...
- Layers pipeline concurrently once the first layer produces output

## Memory System Architecture

```
Controller
├── Front End Processor (FEP)
│   ├── Host Interface
│   ├── Flash Translation Layer (FTL/MML)
│   └── DRAM Management
└── Back End Processor (BEP)
    ├── Memory Operations
    ├── ECC Engine
    └── Toggle Mode Interfaces
        └── Memory Package(s)
            └── Memory Die
                ├── Control Circuitry (310)
                ├── Read/Write Circuits (328) — Sense Amplifiers
                └── Memory Structure (326) — NAND Arrays
                    ├── Plane 0
                    │   ├── Block 0 → NAND Strings → Unit Synapses
                    │   ├── Block 1
                    │   └── ...
                    └── Plane 1
                        └── ...
```

## Mapping to seT6

| Samsung Concept | seT6 Type/Constant | Notes |
|-----------------|---------------------|-------|
| Ternary input {−1,0,+1} | `trit` / `ss_input_t` | Direct mapping, no translation |
| Binary weight {−1,+1} | `ss_weight_t` (int8_t) | Subset of trit values |
| Input 0 (zero) | `TRIT_UNKNOWN` / `SS_INPUT_ZERO` | Detected by ZID circuit |
| Sense amplifier output | `ss_synapse_eval()` return | 1=conducts, 0=blocks |
| Counter value CNT | `ss_dot_result_t.cnt_out` | Conducting synapse count |
| Zero count Z | `ss_dot_result_t.z_count` | From ZID |
| Dot-product P | `ss_dot_result_t.dot_product` | Corrected value |

## File Map

All files are **new additions** — no existing seT6 code was modified.

### Headers (include/set6/)

| File                     | Purpose                                              |
|--------------------------|------------------------------------------------------|
| `samsung_us11170290b2.h` | Top-level: patent ref, types, unit synapse model, voltage encoding, chip caps, HAL state |
| `samsung_nand.h`         | NAND array topology, MMIO register map (4 KB aperture) |
| `samsung_tbn.h`          | TBN engine interface: dot-product, matmul, ZID, DNN inference, activations |

### Implementation (src/)

| File             | Purpose                                                  |
|------------------|----------------------------------------------------------|
| `samsung_hal.c`  | HAL init/shutdown, silicon detection, mode/parallelism config |
| `samsung_tbn.c`  | TBN engine: synapse-level emulation, dot-product (Eq 1 & 2), ZID, matmul, multi-layer DNN |

### Hardware (hw/)

| File                           | Purpose                                     |
|--------------------------------|---------------------------------------------|
| `samsung_us11170290b2.dts`     | Device tree source for platform discovery   |
| `samsung_us11170290b2_zid.v`   | Verilog model: ZID circuit, sense amplifier, unit synapse, multi-block engine |

### Tests (tests/)

| File                           | Purpose                                     |
|--------------------------------|---------------------------------------------|
| `test_samsung_us11170290b2.c`  | 55 tests across 18 categories               |

## Building

### Test Suite

```bash
make test_samsung_us11170290b2
./test_samsung_us11170290b2
```

### Full Test Run (all suites)

```bash
make test
```

## Test Categories

| # | Category | Tests | Description |
|---|----------|-------|-------------|
| 1 | Weight Encoding | 4 | Valid weights, synapse programming, readback |
| 2 | Voltage Patterns | 4 | Input encoding for ±1 and 0 |
| 3 | Cell Conductivity | 3 | Erased/programmed at Vread/Vpass |
| 4 | Unit Synapse | 6 | All 6 patent cases (FIGS 12-15) |
| 5 | ZID | 5 | Zero detection: count, bitmap, edge cases |
| 6 | BNN Dot-Product | 4 | Eq. 1 with all-match/mismatch/mixed/single |
| 7 | TBN Dot-Product | 6 | Eq. 2 with various zero patterns |
| 8 | Auto-Mode | 2 | BNN/TBN dispatch based on HAL mode |
| 9 | Matrix-Vector | 4 | 2×2, 3×4, 1×1, null guards |
| 10 | Activations | 2 | Sign and ternary with threshold |
| 11 | DNN Inference | 1 | Two-layer network end-to-end |
| 12 | HAL Lifecycle | 3 | Init, shutdown, null guards |
| 13 | Mode Config | 3 | BNN/TBN switching, ZID auto-enable |
| 14 | Parallelism | 3 | Sequential, multi-block, pipelined |
| 15 | Weight Prog | 3 | Program, read, null guards |
| 16 | Patent Formulas | 3 | Eq. 1 & 2 explicit verification, XNOR property |
| 17 | Edge Cases | 2 | 64-element vector, sparse 16-element |
| 18 | MMIO Constants | 2 | Register offset ordering, topology packing |

**Total: 55 tests**

## Key Differences from Huawei CN119652311A

| Aspect | Huawei | Samsung |
|--------|--------|---------|
| Technology | CNTFET ternary gates | NAND flash in-memory compute |
| Operation | General-purpose ternary ALU | Neural network inference only |
| Inputs | Ternary {0,1,2} (unbalanced) | Ternary {−1,0,+1} (balanced) |
| Weights | N/A (arbitrary ternary) | Binary {−1,+1} only |
| Core primitive | INC/DEC gates | Unit synapse (SLC pair) |
| Computation | Gate-level: sum, adder, multiplier | Array-level: dot-product, matmul |
| Translation | `hw_val = balanced + 1` | Direct (no translation needed) |
| ZID circuit | N/A | NOR gate array + combinational logic |
| Parallelism | ALU unit count | Block/plane/pipeline hierarchy |

## References

- Samsung Patent US11170290B2 (full text in `SAMSUNG_PATENT_US11170290B2.md`)
- Related patents:
  - US11625586B2: Ternary inputs **and** ternary weights in NAND arrays
  - US11328204B2: Binary neural networks in NAND arrays (BNN only)
  - US11568200B2: Sparse matrix multiplication acceleration
- Academic references:
  - Wan et al., "TBN: Convolutional Neural Network with Ternary Inputs and Binary Weights," ECCV 2018
  - Rastegari et al., "XNOR-Net: ImageNet Classification Using Binary Convolutional Neural Networks," ECCV 2016
