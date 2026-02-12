seT5 Documentation
===================

**Secure Embedded Ternary Microkernel 5** — A formally verified ternary
extension of seL4 using Kleene three-valued logic.

.. toctree::
   :maxdepth: 2
   :caption: Contents

Overview
--------

seT5 extends ANSI C with a first-class ``trit`` type (values: -1/false,
0/unknown, +1/true) using Kleene logic operators. The emulation layer
packs 32 trits into 64-bit registers for near-native binary performance
on commodity hardware.

Key components:

- **trit.h** — Core type and Kleene operators (AND=min, OR=max, NOT=-a)
- **trit_emu.h** — 2-bit packed SIMD emulation (32 trits per uint64_t)
- **trit_cast.h** — Type-safe casting (Bool<->Trit, Int<->Trit)
- **trit_type.h** — Range-checked construction with fault detection
- **TritKleene.thy** — Isabelle/HOL proof stubs for Kleene lattice properties

Performance
-----------

The emulation layer targets:

- **< 0.002s** for 1M Kleene AND operations
- **< 15% overhead** vs native binary AND on 64-bit hardware

This is achieved through:

1. Bit-parallel min/max on 2-bit encoded pairs (~10 ALU instructions)
2. 4x loop unrolling for instruction-level parallelism (128 trits/iteration)
3. Cache-friendly contiguous register arrays
