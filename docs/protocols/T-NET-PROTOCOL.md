# T-NET Protocol — Ternary Network Frame Specification

> **T-023:** RFC-style specification for ternary network communication.
> Version: 1.0 | Status: Draft | Date: 2026-02-18

## Abstract

This document specifies the Ternary Network Protocol (T-NET), a native ternary
frame format for chip-to-chip and node-to-node communication in ternary computing
systems. T-NET uses balanced ternary encoding on the wire, GF(3) Hamming error
correction, and the T-IPC Guardian Trit integrity mechanism.

## 1. Terminology

| Term | Definition |
|------|-----------|
| **Trit** | A balanced ternary digit: {-1 (F), 0 (U), +1 (T)} |
| **Tryte** | 9 trits (range: ±9841) |
| **T-NET Frame** | The fundamental transport unit |
| **Guardian Trit** | Integrity checksum trit appended to payloads |
| **PAM-3** | 3-level Pulse Amplitude Modulation (physical layer) |

## 2. Physical Layer

T-NET operates over PAM-3 signaling, mapping each trit directly to a voltage level:

| Trit Value | PAM-3 Level | Voltage (nominal) |
|-----------|-------------|-------------------|
| -1 (F)   | Level 0     | -V               |
| 0  (U)   | Level 1     |  0               |
| +1 (T)   | Level 2     | +V               |

**Wire rate:** 1 trit per symbol period. At 26.5625 GBd (PAM-3 SerDes), this
yields 26.5625 Gtrit/s raw throughput — 50% more information per symbol than
binary NRZ at the same baud rate.

## 3. Frame Format

```
┌──────────┬─────────┬──────────┬─────────────┬──────────┬──────────┐
│ Preamble │ SFD     │ Header   │ Payload     │ FCS      │ Guardian │
│ 27 trits │ 3 trits │ 18 trits │ 0–729 trits │ 9 trits  │ 1 trit   │
└──────────┴─────────┴──────────┴─────────────┴──────────┴──────────┘
```

### 3.1 Preamble (27 trits)
Alternating `+1, -1, +1, -1, ...` pattern for clock recovery and AGC training.

### 3.2 Start Frame Delimiter (3 trits)
`[+1, +1, 0]` — unique pattern not found in preamble.

### 3.3 Header (18 trits = 2 trytes)
| Field | Trits | Description |
|-------|-------|-------------|
| Version | 3 | Protocol version (balanced ternary, range ±13) |
| Type | 3 | Frame type: DATA(+1), ACK(0), NACK(-1), ... |
| Length | 9 | Payload length in trits (range 0–9841) |
| Priority | 3 | Ternary priority: HIGH(+1), NORMAL(0), LOW(-1) |

### 3.4 Payload (0–729 trits)
Application data. Maximum payload is 729 trits (3^6 = 1 ternary page).

### 3.5 Frame Check Sequence (9 trits)
GF(3) Hamming code computed over Header + Payload:
- Detects all single-trit errors
- Corrects all single-trit errors
- Detects most double-trit errors

### 3.6 Guardian Trit (1 trit)
T-IPC Guardian Trit integrity check:
- Sum all trits in (Header + Payload + FCS) mod 3
- Guardian = negation of sum (ensures total ≡ 0 mod 3)
- Any corruption flips the guardian check

## 4. Error Correction

The FCS uses a (12, 9) GF(3) Hamming code:
- **Parity matrix H** over GF(3) = {0, 1, 2}
- **Syndrome computation:** s = H · r^T mod 3
- **Zero syndrome** → no error
- **Non-zero syndrome** → syndrome column index gives error position

## 5. Flow Control

T-NET uses a 3-state flow control mechanism:

| ACK Trit | Meaning |
|----------|---------|
| +1 (T)   | **ACK** — frame received correctly |
| 0  (U)   | **WAIT** — receiver busy, retransmit later |
| -1 (F)   | **NACK** — frame corrupted, retransmit now |

This eliminates the binary timeout ambiguity: a receiver can explicitly signal
"busy but alive" with the Unknown state, preventing unnecessary retransmissions.

## 6. Compression

Payloads may be Huffman-compressed using the T-IPC ternary Huffman scheme:
- 0 → 1 trit: `[0]`
- +1 → 2 trits: `[+1, +1]`
- -1 → 2 trits: `[+1, -1]`

Average compression: 1.5 trits/symbol for uniform distribution.

## 7. Security

All T-NET frames support optional encryption via the ternary sponge cipher
from `trit_crypto.h`:
- Key exchange: Ternary LWE lattice (NIST FIPS 203 aligned)
- Encryption: GF(3) sponge with mod-3 addition
- MAC: Guardian Trit + sponge hash

## 8. PAM-4 Interoperability

For bridging to IEEE 802.3df PAM-4 links:
- Each PAM-4 symbol (4 levels) carries 1 trit + 1 parity bit
- Trit mapped to levels {0, 1, 2}, level 3 reserved for framing
- Overhead: 33% bandwidth for parity, but provides clean ternary transport
  over existing PAM-4 infrastructure

## 9. References

- seT6 T-IPC: `include/set5/tipc.h`
- seT6 PAM-3/4: `include/set5/pam3_transcode.h`
- seT6 Crypto: `include/set5/trit_crypto.h`
- seT6 GF(3) Hamming: `src/fault_tolerant_network.c`
- IEEE 802.3df PAM-4 specification
- NIST FIPS 203 ML-KEM
