# Ingole WO2016199157A1 Ternary ALU — seT5 Integration Guide

## Patent Reference

| Field       | Value                                                          |
|-------------|----------------------------------------------------------------|
| Patent ID   | WO2016199157A1                                                 |
| Title       | Ternary Arithmetic and Logic Unit (ALU) and Ternary Logic Circuits |
| Assignee    | Individual (Vijay T. Ingole, Indira V. Ingole, Ashutosh V. Ingole, Paritosh V. Ingole) |
| Filed       | 2015-08-03                                                     |
| Published   | 2016-12-15                                                     |
| Application | PCT/IN2015/000307                                              |
| IPC Class   | G06F7/49 (Radix other than binary), G06F7/00                  |
| Status      | Ceased                                                         |
| Cited By    | Huawei WO2025060996A1, IBM US10545727B2, Russian RU2681702C1  |

## Architecture Overview

The WO2016199157A1 patent defines a complete **Ternary Arithmetic and Logic
Unit (TALU)** as the essential building block of a ternary CPU. The TALU uses
**transmission gates (TG)** built from enhancement-mode CMOS (ECMOS) transistors
arranged to minimize interconnections, reduce power, and decrease chip area.

### Key Design Principles

1. **Plurality of parallel stages**: n TALU blocks cascaded for multi-trit words
2. **Single 2-trit decoder (OPCODE)**: 9 outputs controlling all operations
3. **Transmission gate topology**: No resistors/diodes, pure TG switching
4. **Unbalanced ternary {0, 1, 2}**: Three discrete voltage levels
5. **Carry propagation**: Stage-to-stage carry chain for arithmetic

### Logic Values

| WO2016199 | Voltage   | seT5 Balanced | Symbolic      |
|-----------|-----------|---------------|---------------|
| Level 0   | 0V (GND)  | −1            | TRIT_FALSE    |
| Level 1   | VDD/2     |  0            | TRIT_UNKNOWN  |
| Level 2   | VDD       | +1            | TRIT_TRUE     |

**Translation:** `unbalanced = balanced + 1` / `balanced = unbalanced - 1`

### OPCODE Table (2-trit decoder → 9 operations)

| OPCODE (S0,S1) | Decoded Output | Operation              | F01 Output        | F02 Output           |
|----------------|----------------|------------------------|--------------------|----------------------|
| 0,0            | D0 (901)       | NOP                    | —                  | —                    |
| 0,1            | D1 (902)       | All Inclusive TOR/TNOR | All Inc. TOR       | All Inc. TNOR        |
| 0,2            | D2 (903)       | TOR / TNOR             | TOR                | TNOR                 |
| 1,0            | D3 (904)       | All Inclusive TAND/TNAND| All Inc. TAND     | All Inc. TNAND       |
| 1,1            | D4 (905)       | TAND / TNAND           | TAND               | TNAND                |
| 1,2            | D5 (906)       | XTOR / Comparator      | XTOR               | Comparator           |
| 2,0            | D6 (907)       | B−A + Carry            | SUM                | CARRY                |
| 2,1            | D7 (908)       | A−B + Carry            | SUM                | CARRY                |
| 2,2            | D8 (909)       | A+B + Carry            | SUM                | CARRY                |

### Circuit Blocks (22+ output functions)

| Block          | Function                    | TG Count | Description                         |
|----------------|-----------------------------|----------|-------------------------------------|
| ADD 1 CARRY    | 3's complement carry inject | 4 TG     | LST-only for subtraction            |
| TNOT           | Ternary inverter {2,1,0}    | 4 TG     | Zero-sequence complement            |
| CWC            | Clockwise rotate            | 4 TG     | {0→0,1→2,2→1} positive sequence     |
| CCWC           | Counter-clockwise rotate    | 4 TG     | {0→1,1→0,2→2} negative sequence     |
| TAND           | Ternary AND: min(A,B)       | 8 TG     | Consensus gate                      |
| TNAND          | Ternary NAND                | 8 TG     | Inverted TAND                       |
| TOR            | Ternary OR: max(A,B)        | 8 TG     | Accept-any gate                     |
| TNOR           | Ternary NOR                 | 8 TG     | Inverted TOR                        |
| XTOR           | Ternary exclusive-OR        | 14 TG    | XOR for ternary domain              |
| COMPARATOR     | 3-state compare             | 10 TG    | {0=equal, 1=A>B, 2=A<B}            |
| Adder 1 (S1)   | Half-adder sum             | 16 TG    | First-stage partial sum             |
| Adder 2 (S2)   | Full-adder sum             | 6 TG     | S1 + Carry → final SUM             |
| Carry Gen (C2) | Full carry generator        | 6 TG     | Carry from S1, inputs, Cin          |
| Parity Gen     | Even parity (per operand)   | 16 TG    | Identical to Adder 1 topology       |
| 2×9 Decoder    | OPCODE decoder              | 48 TG    | 2 TRIT → 9 decoded control lines    |

### Flags

| Flag          | Source                           | Purpose                    |
|---------------|----------------------------------|----------------------------|
| ALL ZERO      | All Inclusive TOR output         | Detect zero-valued word    |
| OVERFLOW      | Carry output from MST            | Arithmetic overflow detect |
| EVEN PARITY A | Parity generator chain (A)       | Error detection, operand A |
| EVEN PARITY B | Parity generator chain (B)       | Error detection, operand B |

## seT5/seT6 Integration Points

### 1. ISA Mapping

The TALU's 9-operation OPCODE maps directly to seT5 multi-radix instructions:

| seT5 Instruction | TALU OPCODE | Description                     |
|------------------|-------------|---------------------------------|
| `DOT_TRIT`       | S22 (A+B)   | Multiply-accumulate via add     |
| `FFT_STEP`       | S22 + S21   | Butterfly = add + subtract      |
| `RADIX_CONV`     | S22         | Chained addition for conversion |
| Kleene AND       | S11 (TAND)  | Direct logic operation          |
| Kleene OR        | S02 (TOR)   | Direct logic operation          |
| Capability check | S12 (COMP)  | Ternary comparison              |

### 2. Key Advantages for seT6

- **62% more information per trit** vs binary bit (log₂3/log₂2 ≈ 1.585)
- **Processing ratio**: 32-trit processor processes 3³² / 2³² ≈ 4.29 × 10⁹ times more per cycle
- **Component ratio**: 2 × 3ⁿ / 2ⁿ = exponentially better density at higher n
- **No passive components**: Pure TG topology eliminates resistors/diodes
- **Balanced ternary compatible**: Claim 10 explicitly allows balanced mode

### 3. Relationship to Huawei WO2025060996A1

Huawei's 2025 patent (cited in "Cited By") directly builds on this TALU design,
confirming industrial relevance. seT6 bridges both patents by providing a
unified HAL that can target either the Ingole TALU or the Huawei CNTFET ALU.
