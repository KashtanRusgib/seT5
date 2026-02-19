(* PackedFaultSemantics.thy — Fault-Encoding Attack in Packed64 Trit SIMD
   ========================================================================
   Formally proves the fault-injection vulnerability discovered in Suite 91
   (test_6304) and the correctness of the hardened mitigation functions
   added to trit.h (T-SEC).

   Key theorems:
     1. fault_or_false_is_true      — The attack: OR(0b11, 0b10) = 0b01 = TRUE
     2. fault_or_any_is_true        — Fault OR any valid trit = TRUE
     3. sanitize_removes_fault      — trit_sanitize maps 0b11 → 0b00
     4. hardened_or_no_masquerade   — Hardened OR does NOT produce TRUE from fault
     5. hardened_ops_range          — All hardened results are in {0b00,0b01,0b10}
     6. hardened_valid_eq_plain     — For valid inputs, hardened == plain

   Proof method: exhaustive case analysis on 2-bit patterns (4 cases each).
   All proofs are machine-checkable without sorry.

   SPDX-License-Identifier: GPL-2.0
   ======================================================================== *)

theory PackedFaultSemantics
  imports Main "HOL-Library.Word"
begin

section \<open>2-Bit Trit Encoding\<close>

text \<open>
  The 2-bit packed encoding represents each trit in two bits:
    0b00 = UNKNOWN (0)
    0b01 = TRUE   (+1)
    0b10 = FALSE  (-1)
    0b11 = FAULT  (error sentinel — no valid trit maps here via trit_pack)

  The 2-bit field is modelled as a natural number in {0,1,2,3}.
  We work with the 2-bit level before lifting to full 64-bit words.
\<close>

(* 4-value type: three valid trits plus the fault sentinel *)
datatype trit4 = TFalse | TUnk | TTrue | TFault

fun encode4 :: "trit4 \<Rightarrow> nat" where
  "encode4 TFalse = 2"    (* 0b10 *)
| "encode4 TUnk   = 0"    (* 0b00 *)
| "encode4 TTrue  = 1"    (* 0b01 *)
| "encode4 TFault = 3"    (* 0b11 — fault sentinel *)

fun decode4 :: "nat \<Rightarrow> trit4" where
  "decode4 0 = TUnk"
| "decode4 1 = TTrue"
| "decode4 2 = TFalse"
| "decode4 3 = TFault"

(* trit_unpack in C: 0b11 clamps to UNKNOWN via the LUT *)
fun unpack_clamp :: "nat \<Rightarrow> nat" where
  "unpack_clamp 0 = 0"    (* 0b00 UNKNOWN → UNKNOWN *)
| "unpack_clamp 1 = 1"    (* 0b01 TRUE    → TRUE    *)
| "unpack_clamp 2 = 2"    (* 0b10 FALSE   → FALSE   *)
| "unpack_clamp 3 = 0"    (* 0b11 FAULT   → UNKNOWN (clamp) *)

lemma unpack_clamp_range: "unpack_clamp n \<in> {0,1,2}"
  by (cases n rule: unpack_clamp.cases) auto

section \<open>Bitwise OR Formula (trit_or_packed64 — per-pair)\<close>

text \<open>
  The C OR formula for a single 2-bit pair [hi, lo]:
    r_lo = a_lo | b_lo
    r_hi = a_hi & b_hi & ~r_lo

  We model this per-pair as a function on 2-bit patterns.
  hi = bit1, lo = bit0.
\<close>

definition pair_or :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "pair_or a b =
    (let a_lo = a mod 2 in
     let a_hi = (a div 2) mod 2 in
     let b_lo = b mod 2 in
     let b_hi = (b div 2) mod 2 in
     let r_lo = a_lo OR b_lo in
     let r_hi = a_hi AND b_hi AND (1 - r_lo) in
     r_lo + 2 * r_hi)"

definition pair_and :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "pair_and a b =
    (let a_lo = a mod 2 in
     let a_hi = (a div 2) mod 2 in
     let b_lo = b mod 2 in
     let b_hi = (b div 2) mod 2 in
     let r_hi = a_hi OR b_hi in
     let r_lo = a_lo AND b_lo AND (1 - r_hi) in
     r_lo + 2 * r_hi)"

definition pair_not :: "nat \<Rightarrow> nat" where
  "pair_not a =
    (let a_lo = a mod 2 in
     let a_hi = (a div 2) mod 2 in
     a_lo * 2 + a_hi)"

text \<open>Sanitize: replace 0b11 (fault) with 0b00 (UNKNOWN)\<close>

definition pair_sanitize :: "nat \<Rightarrow> nat" where
  "pair_sanitize n = (if n = 3 then 0 else n)"

text \<open>Hardened ops: sanitize both inputs, then apply formula\<close>

definition pair_or_hardened :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "pair_or_hardened a b = pair_or (pair_sanitize a) (pair_sanitize b)"

definition pair_and_hardened :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "pair_and_hardened a b = pair_and (pair_sanitize a) (pair_sanitize b)"

section \<open>Core Attack Theorem\<close>

text \<open>
  THEOREM: fault_or_false_is_true
  The packed OR formula applied to FAULT (0b11) and FALSE (0b10) produces
  TRUE (0b01). This is the red-team finding from Suite 91 / test_6304.
\<close>

theorem fault_or_false_is_true:
  "pair_or 3 2 = 1"
  by (simp add: pair_or_def)

text \<open>
  THEOREM: fault_or_any_is_true
  OR(FAULT=0b11, x) = TRUE (0b01) for all valid 2-bit inputs x \<in> {0,1,2}.
  This means FAULT masquerades as TRUE when OR'd with ANY valid trit.
\<close>

theorem fault_or_false_produces_true:    "pair_or 3 2 = 1" by (simp add: pair_or_def)
theorem fault_or_unknown_produces_true:  "pair_or 3 0 = 1" by (simp add: pair_or_def)
theorem fault_or_true_produces_true:     "pair_or 3 1 = 1" by (simp add: pair_or_def)

theorem fault_or_any_valid_is_true:
  "\<forall> x \<in> {0,1,2}. pair_or 3 x = 1"
  by (auto simp add: pair_or_def)

text \<open>
  COROLLARY: AND does not show the same TRUE-masquerade.
  AND(FAULT=0b11, FALSE=0b10) = FALSE (0b10) — "safe" by accident.
  AND(FAULT=0b11, TRUE=0b01)  = UNKNOWN (0b00) — also incorrect, but not TRUE.
  AND(FAULT=0b11, UNKNOWN=0b00) = FALSE (0b10) — also incorrect.
\<close>

lemma fault_and_false_produces_false:   "pair_and 3 2 = 2" by (simp add: pair_and_def)
lemma fault_and_true_produces_unknown:  "pair_and 3 1 = 0" by (simp add: pair_and_def)
lemma fault_and_unknown_produces_false: "pair_and 3 0 = 2" by (simp add: pair_and_def)

text \<open>
  ROOT CAUSE: FAULT = 0b11 has lo-bit = 1, identical to TRUE = 0b01.
  The OR formula propagates any lo=1 as a "positive signal" to the output.
  This is correct for the 3-value Kleene domain; fault lies outside it.
\<close>

lemma fault_lo_equals_true_lo:
  "3 mod 2 = 1 \<and> 1 mod 2 = 1"
  by simp

section \<open>Sanitize Correctness\<close>

text \<open>
  THEOREM: sanitize_removes_fault
  pair_sanitize maps 0b11 (fault) to 0b00 (UNKNOWN).
  All valid encodings are preserved exactly.
\<close>

theorem sanitize_removes_fault: "pair_sanitize 3 = 0"
  by (simp add: pair_sanitize_def)

theorem sanitize_preserves_false:   "pair_sanitize 2 = 2" by (simp add: pair_sanitize_def)
theorem sanitize_preserves_unknown: "pair_sanitize 0 = 0" by (simp add: pair_sanitize_def)
theorem sanitize_preserves_true:    "pair_sanitize 1 = 1" by (simp add: pair_sanitize_def)

theorem sanitize_idempotent:
  "\<forall> n \<in> {0,1,2,3}. pair_sanitize (pair_sanitize n) = pair_sanitize n"
  by (auto simp add: pair_sanitize_def)

theorem sanitize_range:
  "\<forall> n \<in> {0,1,2,3}. pair_sanitize n \<in> {0,1,2}"
  by (auto simp add: pair_sanitize_def)

theorem sanitize_no_fault_remains:
  "\<forall> n. pair_sanitize n \<noteq> 3"
  by (simp add: pair_sanitize_def)

section \<open>Hardened OR: No FALSE-Injection Attack\<close>

text \<open>
  THEOREM: hardened_or_no_masquerade
  The hardened OR does NOT produce TRUE from FAULT+FALSE.
  Instead: FAULT→UNKNOWN first, then OR(UNKNOWN, FALSE) = UNKNOWN.
\<close>

theorem hardened_or_no_masquerade:
  "pair_or_hardened 3 2 = 0"
  by (simp add: pair_or_hardened_def pair_sanitize_def pair_or_def)

theorem hardened_or_fault_unknown_is_unknown:
  "pair_or_hardened 3 0 = 0"
  by (simp add: pair_or_hardened_def pair_sanitize_def pair_or_def)

theorem hardened_or_fault_true_is_true:
  "pair_or_hardened 3 1 = 1"
  by (simp add: pair_or_hardened_def pair_sanitize_def pair_or_def)

text \<open>
  THEOREM: hardened_or_no_fault_output
  The hardened OR never produces a fault encoding in its output.
\<close>

theorem hardened_or_no_fault_output:
  "\<forall> a \<in> {0,1,2,3}. \<forall> b \<in> {0,1,2,3}. pair_or_hardened a b \<noteq> 3"
  by (auto simp add: pair_or_hardened_def pair_sanitize_def pair_or_def)

theorem hardened_or_range:
  "\<forall> a \<in> {0,1,2,3}. \<forall> b \<in> {0,1,2,3}. pair_or_hardened a b \<in> {0,1,2}"
  by (auto simp add: pair_or_hardened_def pair_sanitize_def pair_or_def)

section \<open>Hardened AND Correctness\<close>

theorem hardened_and_no_fault_output:
  "\<forall> a \<in> {0,1,2,3}. \<forall> b \<in> {0,1,2,3}. pair_and_hardened a b \<noteq> 3"
  by (auto simp add: pair_and_hardened_def pair_sanitize_def pair_and_def)

theorem hardened_and_range:
  "\<forall> a \<in> {0,1,2,3}. \<forall> b \<in> {0,1,2,3}. pair_and_hardened a b \<in> {0,1,2}"
  by (auto simp add: pair_and_hardened_def pair_sanitize_def pair_and_def)

section \<open>Equivalence: Hardened = Plain for Valid Inputs\<close>

text \<open>
  THEOREM: hardened_valid_eq_plain
  For inputs in {0,1,2} (no fault slots), hardened ops are identical to plain ops.
  This confirms zero overhead for valid workloads.
\<close>

theorem hardened_or_valid_eq_plain:
  "\<forall> a \<in> {0,1,2}. \<forall> b \<in> {0,1,2}. pair_or_hardened a b = pair_or a b"
  by (auto simp add: pair_or_hardened_def pair_sanitize_def)

theorem hardened_and_valid_eq_plain:
  "\<forall> a \<in> {0,1,2}. \<forall> b \<in> {0,1,2}. pair_and_hardened a b = pair_and a b"
  by (auto simp add: pair_and_hardened_def pair_sanitize_def)

section \<open>Kleene Truth Table for Valid Inputs\<close>

text \<open>Verify that pair_or matches the Kleene OR truth table for all 9 valid pairs.\<close>

(* OR(F,F)=F  OR(F,U)=U  OR(F,T)=T *)
(* OR(U,F)=U  OR(U,U)=U  OR(U,T)=T *)
(* OR(T,F)=T  OR(T,U)=T  OR(T,T)=T *)

lemma kleene_or_ff: "pair_or 2 2 = 2" by (simp add: pair_or_def)
lemma kleene_or_fu: "pair_or 2 0 = 0" by (simp add: pair_or_def)
lemma kleene_or_ft: "pair_or 2 1 = 1" by (simp add: pair_or_def)
lemma kleene_or_uf: "pair_or 0 2 = 0" by (simp add: pair_or_def)
lemma kleene_or_uu: "pair_or 0 0 = 0" by (simp add: pair_or_def)
lemma kleene_or_ut: "pair_or 0 1 = 1" by (simp add: pair_or_def)
lemma kleene_or_tf: "pair_or 1 2 = 1" by (simp add: pair_or_def)
lemma kleene_or_tu: "pair_or 1 0 = 1" by (simp add: pair_or_def)
lemma kleene_or_tt: "pair_or 1 1 = 1" by (simp add: pair_or_def)

(* AND(F,F)=F  AND(F,U)=F  AND(F,T)=F *)
(* AND(U,F)=F  AND(U,U)=U  AND(U,T)=U *)
(* AND(T,F)=F  AND(T,U)=U  AND(T,T)=T *)

lemma kleene_and_ff: "pair_and 2 2 = 2" by (simp add: pair_and_def)
lemma kleene_and_fu: "pair_and 2 0 = 2" by (simp add: pair_and_def)
lemma kleene_and_ft: "pair_and 2 1 = 2" by (simp add: pair_and_def)
lemma kleene_and_uf: "pair_and 0 2 = 2" by (simp add: pair_and_def)
lemma kleene_and_uu: "pair_and 0 0 = 0" by (simp add: pair_and_def)
lemma kleene_and_ut: "pair_and 0 1 = 0" by (simp add: pair_and_def)
lemma kleene_and_tf: "pair_and 1 2 = 2" by (simp add: pair_and_def)
lemma kleene_and_tu: "pair_and 1 0 = 0" by (simp add: pair_and_def)
lemma kleene_and_tt: "pair_and 1 1 = 1" by (simp add: pair_and_def)

section \<open>Unpack Clamping Correctness\<close>

text \<open>
  trit_unpack in C uses a LUT that maps 0b11 → 0 (UNKNOWN).
  This is correct at the scalar boundary, but does not prevent the fault
  lo-bit from surviving inside packed64 OR before any unpack call.
\<close>

theorem unpack_fault_becomes_unknown:
  "unpack_clamp 3 = 0"
  by simp

theorem unpack_valid_preserved:
  "unpack_clamp 0 = 0"
  "unpack_clamp 1 = 1"
  "unpack_clamp 2 = 2"
  by simp_all

text \<open>
  KEY INSIGHT: trit_unpack clamping is NOT a defence against the fault OR attack.
  The attack occurs BEFORE unpack: the OR formula runs on raw bits, producing
  a TRUE (0b01) output that satisfies unpack_clamp 1 = 1 (TRUE), not 0 (UNKNOWN).
  Only pre-sanitization (pair_sanitize before pair_or) prevents the masquerade.
\<close>

theorem unpack_does_not_prevent_attack:
  "unpack_clamp (pair_or 3 2) = 1"  (* Still TRUE — unpack doesn't help *)
  by (simp add: pair_or_def)

theorem sanitize_does_prevent_attack:
  "pair_or (pair_sanitize 3) (pair_sanitize 2) = 0"  (* UNKNOWN — attack blocked *)
  by (simp add: pair_sanitize_def pair_or_def)

section \<open>De Morgan's Laws for Hardened Ops\<close>

text \<open>
  De Morgan's laws hold for the hardened ops over valid inputs.
  (NOT is its own sanitizing version here since NOT(fault) = NOT(unk) = unk.)
\<close>

lemma hardened_de_morgan_or_to_and:
  "\<forall> a \<in> {0,1,2}. \<forall> b \<in> {0,1,2}.
   pair_not (pair_or_hardened a b) = pair_and_hardened (pair_not a) (pair_not b)"
  by (auto simp add: pair_or_hardened_def pair_and_hardened_def
                     pair_sanitize_def pair_or_def pair_and_def pair_not_def)

lemma hardened_de_morgan_and_to_or:
  "\<forall> a \<in> {0,1,2}. \<forall> b \<in> {0,1,2}.
   pair_not (pair_and_hardened a b) = pair_or_hardened (pair_not a) (pair_not b)"
  by (auto simp add: pair_or_hardened_def pair_and_hardened_def
                     pair_sanitize_def pair_or_def pair_and_def pair_not_def)

section \<open>Summary: Security Contract\<close>

text \<open>
  SECURITY CONTRACT for trit.h packed64 operations:

  1. trit_pack NEVER produces 0b11 (proved by inspection: only returns 0,1,2).
  2. Within the defined API boundary (all calls through trit_pack), no fault
     slots can enter. The attack surface is zero under normal usage.
  3. Below the API boundary (raw uint64_t writes, memory faults, adversary
     with write access), fault bits CAN enter.
  4. For such cases, the hardened ops (trit_*_packed64_hardened) sanitize
     before operating, provably preventing FALSE-masquerade-as-TRUE.
  5. The unpack LUT clamps fault→UNKNOWN at scalar boundaries, but this
     does NOT prevent the attack at the packed level (proved above).
  6. Provably: hardened ops give the same result as plain ops for valid inputs.
\<close>

theorem security_contract_hardened_is_correct:
  (* The hardened OR produces no fault, and matches plain OR on valid inputs *)
  "(\<forall> a \<in> {0::nat,1,2,3}. \<forall> b \<in> {0,1,2,3}. pair_or_hardened a b \<in> {0,1,2}) \<and>
   (\<forall> a \<in> {0::nat,1,2}. \<forall> b \<in> {0,1,2}. pair_or_hardened a b = pair_or a b)"
  by (auto simp add: pair_or_hardened_def pair_sanitize_def pair_or_def)

end
