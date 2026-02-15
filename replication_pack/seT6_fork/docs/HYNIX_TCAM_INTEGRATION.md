# Macronix/Hynix US20230162024A1 — TCAM Crossbar GNN Integration

## Patent Overview

**Patent**: US20230162024A1  
**Assignees**: Macronix International / SK Hynix  
**Title**: TCAM Crossbar for GNN Training Acceleration  
**Filing Date**: 2023  

## Key Innovations

1. **TCAM Crossbar Matrix**: Stores graph edges with content-addressable
   search for O(1) neighbor lookup via hit vector generation.

2. **MAC Crossbar**: Feature accumulation gated by TCAM hit vectors,
   enabling parallel weighted sum computation.

3. **Dynamic Fixed-Point (DFP)**: Reduces exponent grouping from 7 to 2
   groups, cutting MAC cycles from 7 to 2 (3.5× speedup).

4. **Adaptive Data Reusing**: Non-uniform bootstrapping with reduced
   sampling probability for over-represented nodes.

## seT6 Integration

### Source Files

| File | Description |
|------|-------------|
| `include/set6/hynix_tcam.h` | TCAM/MAC/DFP/GNN types and API |
| `src/hynix_tcam.c` | Full implementation (~350 lines) |
| `hw/hynix_tcam_crossbar.v` | Verilog RTL model |
| `hw/hynix_tcam.dts` | Device tree source |

### Architecture

```
┌──────────────────────────────────────────────────┐
│  GNN Training Pipeline                           │
│  ├── tcam_gnn_sample_batch()                     │
│  │   └── Non-uniform bootstrapping               │
│  ├── tcam_gnn_aggregate()                        │
│  │   ├── TCAM search (destination node)          │
│  │   ├── Hit vector generation                   │
│  │   └── MAC accumulation (gated by HV)          │
│  └── tcam_gnn_update()                           │
│      └── Weight matrix × aggregated features     │
├──────────────────────────────────────────────────┤
│  TCAM Crossbar          │  MAC Crossbar          │
│  ├── 64 rows × 32 cols  │  ├── 64 rows           │
│  ├── Edge storage        │  ├── Feature storage   │
│  ├── Search by dst node  │  └── HV-gated accum   │
│  └── Search by vtx+layer │                        │
├──────────────────────────┼────────────────────────┤
│  Dynamic Fixed-Point (DFP)                        │
│  ├── Group 0: exponents 2^0 to 2^-3              │
│  ├── Group 1: exponents 2^-4 to 2^-7             │
│  └── 2-cycle MAC (vs 7-cycle naive)              │
└──────────────────────────────────────────────────┘
```

### TCAM Ternary Semantics

The TCAM naturally maps to seT6's balanced ternary:

| TCAM State | Balanced Trit | Meaning |
|------------|---------------|---------|
| Match | +1 (TRUE) | Entry matches search key |
| Don't-care | 0 (UNKNOWN) | Matches any value |
| Mismatch | -1 (FALSE) | Entry does not match |

### GNN Pipeline Flow

Per patent FIG. 2:

1. **Sample**: Select batch of target nodes (non-uniform bootstrap)
2. **Aggregate**: For each target node:
   - Search TCAM for edges with matching destination
   - Generate hit vector (binary, 64-bit)
   - Feed hit vector to MAC crossbar
   - Accumulate neighbor features + self features
3. **Update**: Apply weight matrix to aggregated features

### Configuration

| Parameter | Value | Source |
|-----------|-------|--------|
| TCAM rows | 64 | Patent FIG. 6 |
| TCAM columns | 32 | Patent FIG. 6 |
| Max nodes | 128 | Simulation limit |
| Max edges | 256 | Simulation limit |
| Feature dimensions | 16 | Patent spec |
| DFP groups | 2 | Patent Table I |
| Max batch size | 32 | Patent FIG. 16 |

### Test Coverage

Tested in `tests/test_tsmc_tmd_intel_pam3_hynix_tcam.c`:
- TCAM crossbar init (zeroed, NULL check)
- Edge insertion (single, multiple, overflow)
- Search by destination (single hit, multiple hits, no hits)
- Search by vertex + layer (exact match, don't-care wildcards)
- Search statistics tracking
- MAC crossbar init and feature insertion
- MAC accumulation with hit vector (gated, empty)
- DFP encode (group 0, group 1, NULL check)
- DFP decode (reconstruction)
- DFP MAC (accumulation, NULL safety)
- GNN init (zeroed, NULL check)
- GNN load graph (TCAM + MAC population)
- GNN sample batch (node selection, range validation)
- GNN aggregate (feature accumulation with exact value check)
- GNN update (identity weight preservation)
- GNN train epoch (full pipeline)
- GNN multi-epoch training
- Invalid node feature access
