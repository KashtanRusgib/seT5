// seT6 Ternary Extension — Casting Rules for Sema
//
// Reference implementation for a Clang fork.
// Integrates into SemaCast.cpp's CheckCStyleCast / CheckStaticCast.
//
// AFP basis: "Three-Valued Logic" — Boolean <-> Kleene embedding.
// Kleene (1952): Two-valued logic is a sublattice of three-valued.
//
// SPDX-License-Identifier: GPL-2.0

#if 0 // Reference implementation — not compiled standalone

#include "clang/Sema/Sema.h"
#include "clang/AST/Type.h"

namespace clang {

/// Casting truth table for trit conversions.
///
/// bool  -> trit:  false -> -1,  true -> +1         (lossless)
/// int   -> trit:  -1/0/+1 pass; else -> error      (checked)
/// trit  -> bool:  -1 -> false, +1 -> true, 0 -> ERROR (partial)
/// trit  -> int:   always valid (widening)           (lossless)
///
/// These mirror the AFP lattice embedding:
///   embed : {F, T} -> {-1, 0, +1}  where embed(F)=-1, embed(T)=+1
///   project: {-1, 0, +1} -> {F, T}  partial, undefined at 0

enum TritCastKind {
  TCK_BoolToTrit,    // lossless embedding
  TCK_IntToTrit,     // range-checked narrowing
  TCK_TritToBool,    // partial — 0 is error
  TCK_TritToInt,     // lossless widening
  TCK_TritToTrit,    // identity
  TCK_Invalid        // e.g., float -> trit
};

/// Determine the appropriate cast kind.
static TritCastKind classifyTritCast(QualType SrcTy, QualType DstTy) {
  const bool srcIsTrit = SrcTy->isTritType();
  const bool dstIsTrit = DstTy->isTritType();
  const bool srcIsBool = SrcTy->isBooleanType();
  const bool dstIsBool = DstTy->isBooleanType();
  const bool srcIsInt  = SrcTy->isIntegerType() && !srcIsBool && !srcIsTrit;
  const bool dstIsInt  = DstTy->isIntegerType() && !dstIsBool && !dstIsTrit;

  if (srcIsTrit && dstIsTrit) return TCK_TritToTrit;
  if (srcIsBool && dstIsTrit) return TCK_BoolToTrit;
  if (srcIsInt  && dstIsTrit) return TCK_IntToTrit;
  if (srcIsTrit && dstIsBool) return TCK_TritToBool;
  if (srcIsTrit && dstIsInt)  return TCK_TritToInt;
  return TCK_Invalid;
}

/// Emit diagnostics for trit casts. Called from CheckCStyleCast.
///
/// Returns true if cast is ill-formed.
static bool checkTritCast(Sema &S, SourceLocation Loc,
                          QualType SrcTy, QualType DstTy,
                          Expr *SrcExpr) {
  TritCastKind kind = classifyTritCast(SrcTy, DstTy);

  switch (kind) {
  case TCK_BoolToTrit:
    // Lossless: false->-1, true->+1.  No diagnostic.
    // Codegen: val = src ? +1 : -1
    return false;

  case TCK_IntToTrit:
    // Warn: narrowing.  Runtime check inserted by CodeGen.
    S.Diag(Loc, diag::warn_trit_narrowing_cast)
        << SrcTy << DstTy;
    return false;

  case TCK_TritToBool:
    // Error if not provably non-unknown at compile time.
    //
    // AFP: project(U) is undefined in the Kleene lattice.
    // We emit a warning and insert a runtime trap for U->bool.
    S.Diag(Loc, diag::warn_trit_to_bool_lossy)
        << "'unknown' (0) has no boolean equivalent";
    return false;

  case TCK_TritToInt:
    // Always safe: -1, 0, +1 all representable in int.
    return false;

  case TCK_TritToTrit:
    return false;

  case TCK_Invalid:
    // e.g., float -> trit
    S.Diag(Loc, diag::err_trit_invalid_cast)
        << SrcTy << DstTy;
    return true;
  }
  return false;
}

} // namespace clang

// ---- Required diagnostic IDs (add to DiagnosticSemaKinds.td) ----
//
// def warn_trit_narrowing_cast : Warning<
//   "narrowing cast from %0 to 'trit'; "
//   "values outside {-1, 0, +1} will trap to unknown">,
//   InGroup<TernaryNarrowing>;
//
// def warn_trit_to_bool_lossy : Warning<
//   "cast from 'trit' to 'bool' is lossy; %0">,
//   InGroup<TernaryLossy>;
//
// def err_trit_invalid_cast : Error<
//   "cannot cast from %0 to %1; "
//   "only integer and boolean types may convert to 'trit'">;

#endif // reference only
