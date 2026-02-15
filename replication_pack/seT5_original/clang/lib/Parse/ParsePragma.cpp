// seT5 Ternary Extension — Pragma Handler Stub for Clang
//
// In a full Clang fork this would be compiled into libclangParse.
// This file documents the required additions to ParsePragma.cpp.
//
// SPDX-License-Identifier: GPL-2.0

#if 0 // Reference implementation — not compiled standalone

#include "clang/Parse/Parser.h"
#include "clang/Lex/Preprocessor.h"

namespace {

/// Handle '#pragma ternary' — enables seT5 ternary mode for the TU.
struct PragmaTernaryHandler : public PragmaHandler {
  PragmaTernaryHandler() : PragmaHandler("ternary") {}

  void HandlePragma(Preprocessor &PP, PragmaIntroducer Introducer,
                    Token &FirstToken) override {
    PP.getDiagnostics().Report(FirstToken.getLocation(),
        PP.getDiagnostics().getCustomDiagID(
            DiagnosticsEngine::Remark,
            "seT5: ternary logic mode enabled"));
    Token Tok;
    PP.Lex(Tok); // consume remainder
  }
};

} // namespace

// Register in Parser::initializePragmaHandlers():
//   PP.AddPragmaHandler(new PragmaTernaryHandler());

#endif // reference only
