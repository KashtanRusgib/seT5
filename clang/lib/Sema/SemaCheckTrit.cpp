// seT5 Ternary Extension — Operator Type-Checking Rules
//
// Integrates into SemaExpr.cpp's CheckBinaryOperands / CheckUnaryOp.
//
// AFP basis: Kleene lattice is NOT a ring — no addition/multiplication.
// Only lattice ops (meet=AND, join=OR) and involution (NOT) are defined.
//
// SPDX-License-Identifier: GPL-2.0

#if 0 // Reference implementation — not compiled standalone

#include "clang/Sema/Sema.h"
#include "clang/AST/Type.h"

namespace clang {

/// Check whether a binary operator is valid for trit operands.
///
/// Valid:  &&, ||, ==, !=  (Kleene lattice ops)
/// Invalid: +, -, *, /, %, <<, >>, &, |, ^  (arithmetic/bitwise)
///
/// Mixed trit/bool: implicit bool->trit promotion with warning.
/// Mixed trit/int:  error — require explicit cast.
///
static bool checkTritBinaryOp(Sema &S, BinaryOperatorKind Opc,
                              Expr *LHS, Expr *RHS,
                              SourceLocation Loc) {
  QualType LT = LHS->getType();
  QualType RT = RHS->getType();
  bool lIsTrit = LT->isTritType();
  bool rIsTrit = RT->isTritType();

  if (!lIsTrit && !rIsTrit) return false; // not our concern

  // Block arithmetic/bitwise on trits
  switch (Opc) {
  case BO_Add: case BO_Sub: case BO_Mul: case BO_Div: case BO_Rem:
  case BO_Shl: case BO_Shr: case BO_And: case BO_Or:  case BO_Xor:
    S.Diag(Loc, diag::err_trit_arithmetic)
        << "arithmetic and bitwise operators are undefined for 'trit'; "
           "use trit_and/trit_or/trit_not instead";
    return true;

  case BO_LAnd: case BO_LOr:
  case BO_EQ:   case BO_NE:
    // Valid Kleene ops — will be lowered to trit_and/trit_or/trit_equiv
    break;

  case BO_LT: case BO_GT: case BO_LE: case BO_GE:
    // Ordering is defined on the lattice (Neg<Unk<Pos)
    // Result type: trit (not bool) — Kleene comparison
    break;

  default:
    break;
  }

  // Mixed operand checks
  if (lIsTrit != rIsTrit) {
    QualType otherTy = lIsTrit ? RT : LT;
    if (otherTy->isBooleanType()) {
      // Implicit bool->trit promotion
      S.Diag(Loc, diag::warn_trit_implicit_bool_promotion)
          << "implicit bool-to-trit promotion in ternary expression";
      // Insert ImplicitCastExpr: BoolToTrit
    } else if (otherTy->isIntegerType()) {
      S.Diag(Loc, diag::err_trit_mixed_int)
          << "cannot mix 'trit' with integer type without explicit cast; "
             "use trit_from_int()";
      return true;
    } else {
      S.Diag(Loc, diag::err_trit_invalid_cast)
          << otherTy << S.Context.TritTy;
      return true;
    }
  }

  return false;
}

/// Check unary operators on trit.
///
/// Valid:   ! (logical not -> Kleene involution)
/// Invalid: ~, ++, --, +, - (arithmetic)
///
static bool checkTritUnaryOp(Sema &S, UnaryOperatorKind Opc,
                             Expr *Operand, SourceLocation Loc) {
  if (!Operand->getType()->isTritType()) return false;

  switch (Opc) {
  case UO_LNot:
    // Valid: maps to trit_not (Kleene involution)
    // Result type: trit (not bool)
    return false;

  case UO_Not:    // bitwise ~
  case UO_PreInc: case UO_PreDec:
  case UO_PostInc: case UO_PostDec:
  case UO_Plus: case UO_Minus:
    S.Diag(Loc, diag::err_trit_arithmetic)
        << "unary arithmetic/bitwise operators are undefined for 'trit'";
    return true;

  default:
    return false;
  }
}

/// Block 'if (trit_expr)' — trit has no implicit bool conversion.
///
/// The user must explicitly collapse via trit_to_bool_safe() or
/// trit_to_bool_strict().  This prevents silent mishandling of
/// the 'unknown' state in control flow.
///
static bool checkTritCondition(Sema &S, Expr *Cond, SourceLocation Loc) {
  if (!Cond->getType()->isTritType()) return false;

  S.Diag(Loc, diag::err_trit_implicit_condition)
      << "'trit' cannot be used as a condition; "
         "use trit_to_bool_safe() or trit_is_definite()";
  return true;
}

// ---- Diagnostic IDs (add to DiagnosticSemaKinds.td) ----
//
// def err_trit_arithmetic : Error<
//   "%0">;
//
// def err_trit_mixed_int : Error<
//   "%0">;
//
// def err_trit_implicit_condition : Error<
//   "%0">;
//
// def warn_trit_implicit_bool_promotion : Warning<
//   "%0">, InGroup<TernaryPromotion>;

} // namespace clang

#endif // reference only
