# Intel/Prodigy US11405248B2 — PAM-3 FPGA Decoder Integration

## Patent Overview

**Patent**: US11405248B2  
**Assignees**: Intel Corporation / Prodigy Technovations  
**Title**: PAM-3 Signal Decoder — FPGA Pipeline  
**Grant Date**: 2022  

## Key Innovations

1. **11-Stage FPGA Pipeline**: Complete PAM-3 signal decoding from oversampled
   ADC input to ternary symbol output.

2. **Slope-Based Level Detection**: Four-threshold comparator with hysteresis
   that adapts based on signal slope direction.

3. **Must-Transition Detection**: Identifies critical +1↔-1 transitions
   within a 12-sample window for timing recovery.

4. **Two-Level Edge Filtering**: Minimum distance filter (≥9 samples) plus
   must-transition proximity filter for robust edge retention.

## seT5 Integration

### Source Files

| File | Description |
|------|-------------|
| `include/set5/intel_pam3_decoder.h` | Full pipeline types and API |
| `src/intel_pam3_decoder.c` | 11-stage implementation (~460 lines) |
| `hw/intel_pam3_decoder.v` | Verilog RTL model |
| `hw/intel_pam3_decoder.dts` | Device tree source |

### Relationship to Existing PAM-3

This module extends the existing `pam3_transcode.{h,c}` which provides basic
PAM-3 encode/decode. The Intel decoder adds a full noise-tolerant
FPGA-based pipeline suitable for real-world signal processing.

### Pipeline Architecture

```
Stage 1:  ADC Sample Loading
    ↓
Stage 2:  DC Correction (128-sample sliding block)
    ↓
Stage 3:  Level Detection (4-threshold + slope)
    ↓
Stage 4:  Spike Filter (single-sample glitch removal)
    ↓
Stage 5:  Edge Detection (transitions + must-transitions)
    ↓
Stage 6:  Midpoint Detection (must-transition centers)
    ↓
Stage 7:  First-Level Edge Filter (≥9 sample distance)
    ↓
Stage 8:  Second-Level Edge Filter (must-transition proximity)
    ↓
Stage 9:  Sampling Point Calculation
    ↓
Stage 10: Sampling Point Filter
    ↓
Stage 11: Symbol Generation → trit output
```

### Key Parameters

| Parameter | Value | Source |
|-----------|-------|--------|
| Oversampling ratio | 12× | Patent spec |
| DC block length | 128 samples | Patent spec |
| Plus threshold | 140 | Patent FIG. 4E |
| Minus threshold | 95 | Patent FIG. 4E |
| Zero+ threshold | 160 | Patent FIG. 4E |
| Zero- threshold | 80 | Patent FIG. 4E |
| Must-transition window | 12 samples | Patent spec |
| Min edge distance | 9 samples | Patent spec |
| Edge lookahead | 4 samples | Patent spec |

### PAM-3 to Balanced Ternary Mapping

| PAM-3 Level | ADC Range | Balanced Trit |
|-------------|-----------|---------------|
| +1 | > 140 (rising) | TRIT_TRUE (+1) |
| 0 | 80–160 | TRIT_UNKNOWN (0) |
| -1 | < 95 (falling) | TRIT_FALSE (-1) |

### Test Coverage

Tested in `tests/test_tsmc_tmd_intel_pam3_hynix_tcam.c`:
- Initialization (defaults, NULL check, custom thresholds)
- DC correction toggle
- Test signal generation (clean, noisy, empty)
- Sample loading (basic, overflow)
- Full pipeline decode (clean signal, noisy signal)
- Individual stages (DC correction, level detection, spike filter, edge detection)
- Statistics accumulation
