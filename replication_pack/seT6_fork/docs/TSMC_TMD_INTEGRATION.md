# TSMC US20230307234A1 — TMD Heterostack Integration

## Patent Overview

**Patent**: US20230307234A1  
**Assignee**: TSMC (Taiwan Semiconductor Manufacturing Company)  
**Title**: 2D Material Heterostack — TMD FET Channels  
**Filing Date**: 2023  

## Key Innovations

1. **2D Material Heterostacks**: Stacking transition metal dichalcogenide (TMD)
   monolayers (MoS2, WS2, MoSe2, WSe2, MoTe2) with hexagonal boron nitride
   (h-BN) insulator layers via van der Waals bonding.

2. **TMD FET Channels**: Using the heterostack as a transistor channel region
   with ternary threshold voltages (V/3 and 2V/3) for three-level logic.

3. **3D Monolithic Integration**: Stacking FEOL silicon, BEOL interconnects,
   and TMD device tiers without thermal budget constraints.

4. **Carrier Film Transfer**: PMMA/PVA/PPC polymer-based wafer transfer with
   residue characterization.

## seT6 Integration

### Source Files

| File | Description |
|------|-------------|
| `include/set6/tsmc_tmd.h` | Full API: monolayer, heterostack, FET, 3D model |
| `src/tsmc_tmd.c` | Implementation (~340 lines) |
| `hw/tsmc_tmd_fet.v` | Verilog simulation model |
| `hw/tsmc_tmd.dts` | Device tree source for platform binding |

### Architecture

```
┌──────────────────────────────────────────────────┐
│  Application Layer (user space)                  │
│  └── tmd_monolayer_create()                      │
│  └── tmd_stack_init() / add_layer() / set_bond() │
│  └── tmd_fet_init() / evaluate() / ternary_not() │
│  └── tmd_3d_init() / density() / validate()     │
├──────────────────────────────────────────────────┤
│  seT6 Microkernel (UNMODIFIED)                   │
│  └── Balanced ternary trit type                  │
│  └── Kleene logic operations                     │
├──────────────────────────────────────────────────┤
│  Hardware Abstraction                            │
│  └── tsmc_tmd_fet.v (Verilog RTL)               │
│  └── tsmc_tmd.dts (Device Tree)                  │
└──────────────────────────────────────────────────┘
```

### Material Properties

| Material | Type | Thickness (pm) | Bandgap (eV) |
|----------|------|----------------|--------------|
| h-BN | Insulator | 330 | ~6.0 |
| MoS2 | Semiconductor | 650 | ~1.8 |
| WS2 | Semiconductor | 620 | ~2.0 |
| MoSe2 | Semiconductor | 700 | ~1.5 |
| WSe2 | Semiconductor | 680 | ~1.6 |
| MoTe2 | Semiconductor | 750 | ~1.0 |
| Graphene | Semimetal | 335 | ~0 |

### Ternary FET Operation

The TMD FET implements balanced ternary logic:

- **Vgate < Vsupply/3** → output = -1 (TRIT_FALSE)
- **Vsupply/3 ≤ Vgate < 2·Vsupply/3** → output = 0 (TRIT_UNKNOWN)
- **Vgate ≥ 2·Vsupply/3** → output = +1 (TRIT_TRUE)

Ternary gates (NOT, AND, OR) use Kleene logic semantics.

### Quality Scoring

Stack quality (0–100) considers:
- Vacuum level during bonding (lower = better)
- Bond force within patent range (60–1600 N/in²)
- Interface residue levels (0 ppm = perfect)
- Layer count penalty

### Test Coverage

All functions tested in `tests/test_tsmc_tmd_intel_pam3_hynix_tcam.c`:
- Monolayer creation (all 7 materials + NULL check)
- Material classification (semiconductor vs dielectric)
- Heterostack operations (init, add, sandwich validation, thickness)
- Bonding parameters (valid, boundary, out-of-range)
- Carrier film (attach/remove)
- Quality scoring (perfect stack, range check)
- FET evaluation (low/mid/high thresholds)
- Ternary gates (NOT, AND, OR truth tables)
- On-current estimation
- 3D model (init, density, validation)
