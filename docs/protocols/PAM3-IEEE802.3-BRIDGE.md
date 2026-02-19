# T-040: PAM-3 to IEEE 802.3df PAM-4 Bridge Specification

> Formal specification bridging seT6's PAM-3 transcoder to IEEE 802.3df PAM-4.
> Version: 1.0 | Date: 2026-02-18

## 1. Overview

This specification defines a protocol bridge between seT6's native PAM-3
(3-level) signaling and the IEEE 802.3df PAM-4 (4-level) physical layer
standard used in 100/200/400 GbE data center interconnects.

The bridge enables ternary-native systems to communicate over existing
PAM-4 SerDes infrastructure without modification to the analog front-end.

## 2. Symbol Mapping

### 2.1 PAM-3 → PAM-4 Encoding

| Trit Value | PAM-3 Level | PAM-4 Level | Notes |
|-----------|-------------|-------------|-------|
| -1 (F)   | Level 0     | Level 0     | Direct map |
| 0  (U)   | Level 1     | Level 1     | Direct map |
| +1 (T)   | Level 2     | Level 2     | Direct map |
| —         | —           | Level 3     | Reserved: sync/control |

### 2.2 PAM-4 → PAM-3 Decoding

| PAM-4 Level | Trit Value | Action |
|-------------|-----------|--------|
| Level 0     | -1 (F)   | Direct decode |
| Level 1     | 0  (U)   | Direct decode |
| Level 2     | +1 (T)   | Direct decode |
| Level 3     | —         | Control symbol (strip from data path) |

### 2.3 Bandwidth Analysis

- **PAM-4 raw capacity:** 2 bits/symbol = 4 levels
- **Ternary content:** log₂(3) ≈ 1.585 bits/symbol = 3 levels
- **Overhead:** 1 unused level per symbol = 25% amplitude overhead
- **Effective throughput:** 79.2% of PAM-4 raw rate for ternary data
- At 53.125 GBd (400GbE): ~42.1 Gtrit/s effective ternary throughput

## 3. Link Training

### 3.1 Training Sequence

The PAM-3/PAM-4 bridge uses a modified 802.3df link training protocol:

1. **Phase 1: PAM-4 standard training** — Transmit 802.3df PRBS13Q patterns
2. **Phase 2: Ternary capability exchange** — Send special frame:
   - Pattern: [3, 0, 1, 2, 0, 1, 2, ...] (Level 3 = capability marker)
   - If peer echoes Level 3 markers, both sides support ternary
3. **Phase 3: Trit mode activation** — Switch to PAM-3 data encoding

### 3.2 Fallback

If the peer does not respond with Level 3 markers, the link operates in
standard PAM-4 binary mode. No ternary data is transmitted.

## 4. Error Detection

### 4.1 Level 3 as Error Indicator

In ternary data mode, any received Level 3 symbol indicates:
- Physical layer error (noise causing level 3 detection)
- Control/management frame (intentional Level 3 insertion)

The receiver counts Level 3 occurrences per frame as a link quality metric.

### 4.2 FCS Integration

The T-NET FCS (GF(3) Hamming) provides ternary-native error correction
independent of the PAM-4 FEC layer, creating a defense-in-depth stack:

1. PAM-4 RS(544,514) FEC — corrects symbol errors
2. PAM-3 Level 3 detection — flags remaining errors
3. GF(3) Hamming FCS — corrects single trit errors
4. Guardian Trit — final integrity check

## 5. Implementation

The bridge is implemented in two C modules:
- `src/pam3_transcode.c` — PAM-3/4 encode/decode with eye diagram
- `include/set5/pam3_transcode.h` — API declarations

And one Verilog module:
- `hw/intel_pam3_decoder.v` — Hardware PAM-3 decoder aligned with Intel patent

## 6. References

- IEEE 802.3df-2025: 100/200/400 Gb/s over PAM-4
- seT6 PAM-3 Transcode: `pam3_transcode.h`
- Intel PAM-3 Decoder Patent integration: `docs/INTEL_PAM3_DECODER_INTEGRATION.md`
- T-NET Protocol: `docs/protocols/T-NET-PROTOCOL.md`
