# seT5/seT6 Replication Pack

Self-contained archive for replicating both the **seT5 perfected baseline**
and the **seT6 development fork** of the Secure Embedded Ternary Microkernel.

## Contents

| Directory          | Description |
|--------------------|-------------|
| `seT5_original/`   | Frozen seT5 baseline — original, unchanged source. Zero-error microkernel. |
| `seT6_fork/`       | Active seT6 fork — all expansions (Sigma 9, RNS, Peirce, TriLang, etc.) |
| `build_repl.sh`    | Build & test both projects from clean state. |
| `verify_repl.sh`   | Diff seT5/seT6, lint for binary creep, radix guard scan, pass-rate check. |

## Quick Start

```bash
unzip seT5_seT6_replication_pack.zip
cd replication_pack
chmod +x build_repl.sh verify_repl.sh
./build_repl.sh        # Build and test both seT5 and seT6
./verify_repl.sh       # Structural verification, lint, radix guard
```

## Expected Results

- **seT5**: ~1147 tests, 100% pass rate
- **seT6**: 3272+ tests across 38 suites, 100% pass rate (Sigma 9 compliant)
- **verify_repl.sh**: 0 binary creep, 0 non-ternary contamination

## Integrity

- seT5_original contains **no "seT6" references** in C/H source files
- seT6_fork contains **no compiled binaries** — everything builds from source
- Both share the same compiler submodule (Ternary-C-compiler)
- All patent docs, proofs, and hardware descriptions included in each copy

## License

GPL-2.0 — See LICENSE in each directory.
