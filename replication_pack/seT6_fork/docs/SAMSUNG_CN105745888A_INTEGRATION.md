# Samsung CN105745888A — Ternary Sequence Communication Integration

## Patent Reference

| Field | Value |
|-------|-------|
| Patent | **CN105745888A** (CN105745888B granted) |
| Korean family | **KR102349122B1** |
| Title | Method and system using ternary sequences for simultaneous transmission to coherent and non-coherent receivers |
| Filed | 2013-10-29 (IN4875/CHE/2013) |
| Granted | 2019-11-26 |
| Assignee | Samsung Electronics Co., Ltd. |
| Classification | H04L25/4923 (ternary codes), H04L25/03834, H04B1/709 |
| Claims | 28 |

## Architecture Overview

CN105745888A defines a **ternary communication protocol** for simultaneously
transmitting data to both **coherent** and **non-coherent** receivers using
cyclic shifts of a base ternary sequence.

### Ternary Alphabet

Identical to seT6's balanced ternary:

| Patent | seT6 | Meaning |
|--------|------|---------|
| -1 | `TRIT_FALSE` (-1) | Negative |
| 0 | `TRIT_UNKNOWN` (0) | Zero / Unknown |
| +1 | `TRIT_TRUE` (+1) | Positive |

**No translation needed** — direct 1:1 mapping.

### Core Protocol

```
Data → k-bit symbols → Cyclic-shift encoding → Ternary sequence TX
                                                        ↓
                                    ┌──────────────────┬──────────────────┐
                                    │  Coherent RX     │  Non-coherent RX │
                                    │  Correlate with  │  Correlate with  │
                                    │  base shifts     │  |base| shifts   │
                                    │  {-1, 0, +1}     │  {0, 1}          │
                                    └──────────────────┴──────────────────┘
                                    │
                                    ↓
                            argmax(Corr_g) → g_est → f⁻¹(g_est) → symbol
```

### Key Equations

**Codeset** (Eq. 2):
```
C = { c_g : c_g = L^g{tb}, ∀ g ∈ Z_N }
```

**Coherent correlation** (Eq. 6):
```
Corr_g = Σ y_c(i) · c_g(i),  ∀ g ∈ Z_N
```

**Non-coherent correlation** (Eq. 7):
```
Corr_g = Σ y_nc(i) · |c_g(i)|,  ∀ g ∈ Z_N
```

**Symbol detection** (Eq. 4):
```
s_est = f⁻¹(g_est),  where g_est = argmax(Corr_g)
```

**MSAC** (Eq. 11):
```
μ_MSAC = (1/(N-1)) · Σ R(τ)²,  τ = 1..P-1
```

### OOK Families (Table 4)

| Name | k (bits) | N (seq len) | Symbol rate |
|------|----------|-------------|-------------|
| 3/8-OOK | 3 | 8 | 3 bits/symbol |
| 4/16-OOK | 4 | 16 | 4 bits/symbol |
| 5/32-OOK | 5 | 32 | 5 bits/symbol |

### Base Sequence Generation Pipeline

```
Seed sequence (m-seq or complement)
  │
  ├── Weight is perfect square?
  │     ├── YES → Preferred-pair cross-correlation → Shift → Divide
  │     │         → Perfect ternary sequence
  │     └── NO  → Invert positions, search min MSAC
  │               → Near-perfect ternary sequence
  │
  └── Insert predefined value at min-MSAC position
      (0 for m-seq seed, 1 for complement seed)
      → Base ternary sequence of length N
```

## File Map

### Headers

| File | Purpose |
|------|---------|
| `include/set6/samsung_tseq.h` | Core types, sequence generation API, inline utilities |
| `include/set6/samsung_tseq_modem.h` | Modem TX/RX interface, symbol mapping, frame types |
| `include/set6/samsung_tseq_mmio.h` | MMIO register map (4 KB at 0x40300000), emulated state |

### Implementation

| File | Purpose |
|------|---------|
| `src/samsung_tseq.c` | m-sequence LFSR, cross-correlation, perfect/near-perfect generation, MSAC, base formation, Table 3 sequences, codeset construction |
| `src/samsung_tseq_modem.c` | Modem init, modulation (cyclic-shift lookup), demodulation (correlation + argmax), frame TX/RX, SNR estimation, noise injection |

### Hardware

| File | Purpose |
|------|---------|
| `hw/samsung_cn105745888a.dts` | Device tree source for ternary sequence modem IP |
| `hw/samsung_cn105745888a_correlator.v` | Verilog: parallel correlator bank, argmax, cyclic shifter, abs projector |

### Tests

| File | Tests | Coverage |
|------|-------|----------|
| `tests/test_samsung_cn105745888a.c` | 55 | 28 categories: trit compat, weight, perfect-square, m-seq, complement, cross-corr, perfect/near-perfect gen, MSAC, aperiodic autocorr, base gen, Table 3, cyclic shift, abs projection, codeset, decimal/Gray mapping, modem lifecycle, modulation, coherent/non-coherent demod, frame TX/RX, round-trip, noise robustness, SNR, families, MMIO, correlation correctness |

## Build & Test

```bash
# Build the test suite
make test_samsung_cn105745888a

# Run tests
./test_samsung_cn105745888a

# Full suite (includes all existing tests + CN105745888A)
make test
```

## Comparison with Other Samsung Patents

| Aspect | US11170290B2 (NAND Inference) | CN105745888A (Ternary Comm) |
|--------|-------------------------------|------------------------------|
| **Domain** | In-memory computing | Wireless communication |
| **Ternary use** | Input encoding {-1,0,+1} | Modulation alphabet {-1,0,+1} |
| **Binary aspect** | Binary weights {-1,+1} | Envelope detection {0,1} |
| **Key operation** | Dot-product (MAC in NAND) | Correlation (cyclic shifts) |
| **Hardware** | NAND flash arrays | Digital correlator bank |
| **seT6 mapping** | Direct (trit = input) | Direct (trit = sequence elem) |
| **Parallelism** | Multi-block/plane/pipeline | N-way parallel correlators |
| **Application** | Neural network inference | Low-power sensor/PAN/BAN |

## seT6 Integration Notes

1. **Zero translation overhead**: seT6's `trit` type maps directly to the
   patent's ternary alphabet — no encoding/decoding needed.

2. **IPC synergy**: Ternary sequences can be used as seT6 IPC message
   encoding for error-resilient inter-process communication.

3. **Multi-radix bridge**: The cyclic-shift codeset structure is compatible
   with seT6's multi-radix framework — base-3 arithmetic maps naturally
   to ternary sequence operations.

4. **Dual-mode reception**: A single seT6 transmitter can serve both
   sophisticated (coherent) and simple (non-coherent) receivers without
   protocol changes — important for mixed-capability IoT networks.

5. **Hardware acceleration**: The Verilog correlator model enables
   FPGA-based acceleration of the demodulation pipeline.

## SPDX-License-Identifier: GPL-2.0
