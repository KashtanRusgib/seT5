# seT6 Solutions & Resources Index

> Cross-reference for proofs, papers, code, and tools.

---

## 1. Core Mathematical Foundations

### De Morgan's Laws (NOT / AND / OR proofs)

    not(a AND b) = (not a) OR (not b)
    not(a OR  b) = (not a) AND (not b)

- **Proved in:** `proof/TritKleene.thy` — lemmas `de_morgan_and`, `de_morgan_or`
- **Runtime:** `trit_not(trit_and(a,b)) == trit_or(trit_not(a), trit_not(b))` in `include/set6/trit.h`
- **Tested:** `demo/trit_emu_bench.c` — scalar + reg32 De Morgan checks

### Kleene Lattice (K3)

| Property                   | Formula                              | Proof File             |
|----------------------------|--------------------------------------|------------------------|
| AND = meet                 | a AND b = min(a,b)                   | TritKleene.thy         |
| OR = join                  | a OR b = max(a,b)                    | TritKleene.thy         |
| NOT = involution           | not(not(a)) = a                      | TritKleene.thy         |
| Unknown absorb (AND)       | U AND T = U                          | TritKleene.thy         |
| Unknown absorb (OR)        | U OR F = U                           | TritKleene.thy         |
| Binary subset collapse     | a,b in {F,T} => Kleene = classical   | TritKleene.thy         |
| Commutativity (AND/OR)     | a AND b = b AND a                    | TritKleene.thy         |
| Associativity (AND)        | (a AND b) AND c = a AND (b AND c)   | TritKleene.thy         |
| Distributivity             | a AND (b OR c) = (a AND b) OR (a AND c) | **TritOps.thy (WP4)** |
| Unknown propagation (AND)  | a != F => U AND a = U                | **TritOps.thy (WP4)**  |
| Monotonicity (AND)         | a<=a', b<=b' => (a AND b)<=(a' AND b') | **TritOps.thy (WP4)** |
| Kleene non-complement      | U AND (not U) = U != F               | **TritOps.thy (WP4)**  |

### Markov Chain — Unknown Convergence

Stationary distribution: pi_U = 0 under alpha > 0
(unknown always resolves). See ARCHITECTURE.md section 3.

## 2. Archive of Formal Proofs (AFP)

| AFP Entry                    | URL                                                          | Use in seT6                                         |
|------------------------------|--------------------------------------------------------------|-----------------------------------------------------|
| Three-Valued Logic           | https://www.isa-afp.org/entries/Three_Valued_Logic.html      | Lattice theory, Kleene truth tables                 |
| Kleene Algebra               | https://www.isa-afp.org/entries/Kleene_Algebra.html          | Idempotent semirings for program semantics           |
| Kleene Algebra with Tests    | https://www.isa-afp.org/entries/KAT_and_DRA.html            | Ternary KAT lifting (guards from Bool to Trit)      |
| Modal Kleene Algebra         | https://www.isa-afp.org/entries/Modal_Kleene_Algebra.html   | Possibility/necessity for unknown propagation        |
| AutoCorres                   | https://www.isa-afp.org/entries/AutoCorres.html              | C parser for Isabelle; extend for `trit` type        |

## 3. Historical & Hardware References

| Source                 | Citation                                                  | Relevance                                 |
|------------------------|-----------------------------------------------------------|-------------------------------------------|
| Setun computer         | Brusentsov, N.P. (1958)                                   | Original balanced ternary; validates {-1,0,+1} |
| CNTFET ternary gates   | Various (2010-2023)                                       | Native ternary hardware target (Phase 4)  |
| Blackham WCET          | Blackham et al. (2011), IEEE RTSS                         | WCET methodology for performance gates    |

## 4. seL4 Verification Chain

| Artifact              | Source                                                      | Notes                                     |
|-----------------------|-------------------------------------------------------------|-------------------------------------------|
| Whitepaper            | `seL4_whitepaper_and_reviews.md` (local)                    | Annotated with ternary implications       |
| Abstract Model (HOL)  | seL4 GitHub `l4v/` repo                                     | Target for `bool -> trit` lifting         |
| Executable Spec (C)   | seL4 GitHub `src/`                                          | Add trit emulation layer                  |
| Refinement Proofs      | seL4 GitHub `l4v/proof/`                                   | ~1M lines; lift ~10% for ternary          |
| CapDL                  | seL4 tools                                                  | Capability distribution; extend for trits |

## 5. Clang / LLVM References

| Resource           | URL / Location                                               | Notes                                     |
|--------------------|--------------------------------------------------------------|-------------------------------------------|
| Clang source       | https://github.com/llvm/llvm-project/tree/main/clang        | Fork target for seT6 extensions           |
| BuiltinTypes.def   | `clang/include/clang/Basic/BuiltinTypes.def` (local stub)   | Add `BUILTIN_TYPE(Trit, TritTy)`          |
| TokenKinds.def     | `clang/include/clang/Basic/TokenKinds.def` (local stub)     | Add `KEYWORD(trit, KEYALL)`               |
| SemaCheckTrit.cpp   | `clang/lib/Sema/SemaCheckTrit.cpp` (local reference)       | Operator type-checking rules              |
| SemaCastTrit.cpp    | `clang/lib/Sema/SemaCastTrit.cpp` (local reference)        | Cast rules (embed/project)                |
| ParsePragma.cpp     | `clang/lib/Parse/ParsePragma.cpp` (local reference)        | `#pragma ternary` handler                 |

## 6. Codebase Quick Reference

| File                         | Purpose                            | Key Symbols                                       |
|------------------------------|------------------------------------|----------------------------------------------------|
| `include/set6/trit.h`       | Core types + Kleene ops            | `trit_and`, `trit_or`, `trit_not`, `trit_pack`    |
| `include/set6/trit_cast.h`  | Bool <-> Trit casting              | `trit_from_bool`, `trit_to_bool_strict`            |
| `include/set6/trit_type.h`  | Type safety + checked construction | `trit_checked`                                     |
| `include/set6/trit_emu.h`   | 2-bit packed SIMD                  | `trit2_and`, `trit2_reg32_and_bulk`                |
| `proof/TritKleene.thy`      | Lattice, De Morgan, absorption     | `trit_and_def`, `de_morgan_and`, `involution`      |
| `proof/TritOps.thy`         | WP4: algebraic properties          | `trit_and_or_distrib`, `unknown_and_propagation`   |

## 7. Build Commands

```bash
# C demos
gcc -std=c99 -O2 -Iinclude -o demo/trit_demo demo/trit_demo.c
gcc -std=c99 -O2 -Iinclude -o demo/trit_type_demo demo/trit_type_demo.c
gcc -std=c99 -D_POSIX_C_SOURCE=200809L -O2 -Iinclude -o demo/trit_emu_bench demo/trit_emu_bench.c

# Run benchmark (gate: <0.002s, <5% overhead)
./demo/trit_emu_bench

# Isabelle proof check (requires Isabelle2024+)
isabelle build -d proof -b TritKleene
isabelle build -d proof -b TritOps
```


---

## Test Documentation Rule

> **MANDATORY**: All new tests MUST have a corresponding entry appended to
> [`TESTS_GLOSSARY_OF_ALL_TESTS.md`](TESTS_GLOSSARY_OF_ALL_TESTS.md) before
> the commit is considered complete. Each entry must include: suite assignment,
> line number, test description, section, assertion expression, and category.
> See the glossary for format details.
