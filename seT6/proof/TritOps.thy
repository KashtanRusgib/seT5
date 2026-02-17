(* -----------------------------------------------------------------------
   seT6 WP4 — Ternary Operator Properties
   
   Extends TritKleene.thy with algebraic laws for Kleene AND/OR/NOT.
   TritKleene already proves: trit_and_comm, trit_and_assoc,
   trit_or_comm, trit_not_involution, de_morgan_and, de_morgan_or,
   unknown_and_absorb, unknown_or_absorb, binary_subset_and.

   This theory adds:
     WP4-A: distributivity, OR associativity                [Prover]
     WP4-B: identity, annihilator, idempotence, absorption,
            unknown propagation, monotonicity (FO+lfp)      [Prover]
     WP4-C: Sepref refinement stubs, Ternary KAT stubs      [Prover]

   Proof method: exhaustive case split over finite datatype trit.
   All lemmas discharge via (cases a; cases b; cases c) auto.

   AFP basis: "Three-Valued Logic", "Kleene Algebra with Tests"
   Encoding: Neg < Unk < Pos  (balanced ternary, T=11 in 2-bit packed)

   SPDX-License-Identifier: GPL-2.0
   ----------------------------------------------------------------------- *)

theory TritOps
  imports TritKleene
begin

(* ===================================================================== *)
section \<open>WP4-A: Distributivity\<close>
(* Note: comm + assoc already in TritKleene.thy                          *)
(* ===================================================================== *)

lemma trit_or_assoc:
  "trit_or (trit_or a b) c = trit_or a (trit_or b c)"
  unfolding trit_or_def by (cases a; cases b; cases c) auto

lemma trit_and_or_distrib:
  "trit_and a (trit_or b c) = trit_or (trit_and a b) (trit_and a c)"
  unfolding trit_and_def trit_or_def by (cases a; cases b; cases c) auto

lemma trit_or_and_distrib:
  "trit_or a (trit_and b c) = trit_and (trit_or a b) (trit_or a c)"
  unfolding trit_and_def trit_or_def by (cases a; cases b; cases c) auto


(* ===================================================================== *)
section \<open>WP4-B: Identity and Annihilator Elements\<close>
(* ===================================================================== *)

(* Pos is AND-identity (lattice top) *)
lemma trit_and_identity: "trit_and a Pos = a"
  unfolding trit_and_def by (cases a) auto

lemma trit_and_identity_left: "trit_and Pos a = a"
  unfolding trit_and_def by (cases a) auto

(* Neg is AND-annihilator (lattice bottom) *)
lemma trit_and_annihilator: "trit_and a Neg = Neg"
  unfolding trit_and_def by (cases a) auto

(* Neg is OR-identity *)
lemma trit_or_identity: "trit_or a Neg = a"
  unfolding trit_or_def by (cases a) auto

(* Pos is OR-annihilator *)
lemma trit_or_annihilator: "trit_or a Pos = Pos"
  unfolding trit_or_def by (cases a) auto


(* ===================================================================== *)
section \<open>WP4-B: Idempotence\<close>
(* ===================================================================== *)

lemma trit_and_idem: "trit_and a a = a"
  unfolding trit_and_def by (cases a) auto

lemma trit_or_idem: "trit_or a a = a"
  unfolding trit_or_def by (cases a) auto


(* ===================================================================== *)
section \<open>WP4-B: Absorption Laws\<close>
(* ===================================================================== *)

lemma trit_and_or_absorb: "trit_and a (trit_or a b) = a"
  unfolding trit_and_def trit_or_def by (cases a; cases b) auto

lemma trit_or_and_absorb: "trit_or a (trit_and a b) = a"
  unfolding trit_and_def trit_or_def by (cases a; cases b) auto


(* ===================================================================== *)
section \<open>WP4-B: Unknown Propagation (Kleene-specific)\<close>
(* The defining feature separating K3 from Boolean algebra               *)
(* ===================================================================== *)

(* AND: Unknown propagates unless the other operand is False *)
lemma unknown_and_propagation:
  "a \<noteq> Neg \<Longrightarrow> trit_and Unk a = Unk"
  unfolding trit_and_def by (cases a) auto

(* OR: Unknown propagates unless the other operand is True *)
lemma unknown_or_propagation:
  "a \<noteq> Pos \<Longrightarrow> trit_or Unk a = Unk"
  unfolding trit_or_def by (cases a) auto

(* NOT(Unknown) = Unknown — fixed point of involution *)
lemma unknown_not_fixed: "trit_not Unk = Unk"
  by simp

(* Unknown is self-idempotent under all ops *)
lemma unknown_and_self: "trit_and Unk Unk = Unk"
  unfolding trit_and_def by simp

lemma unknown_or_self: "trit_or Unk Unk = Unk"
  unfolding trit_or_def by simp


(* ===================================================================== *)
section \<open>WP4-B: Monotonicity (FO+lfp foundation)\<close>
(* Enables Knaster-Tarski fixed-point existence on the Kleene lattice    *)
(* AFP ref: lattice fixed-point theory needs monotone operators          *)
(* ===================================================================== *)

lemma trit_and_mono:
  "a \<le> a' \<Longrightarrow> b \<le> b' \<Longrightarrow> trit_and a b \<le> trit_and a' b'"
  unfolding trit_and_def by (cases a; cases a'; cases b; cases b') auto

lemma trit_or_mono:
  "a \<le> a' \<Longrightarrow> b \<le> b' \<Longrightarrow> trit_or a b \<le> trit_or a' b'"
  unfolding trit_or_def by (cases a; cases a'; cases b; cases b') auto

(* NOT is antitone (order-reversing) *)
lemma trit_not_antitone:
  "a \<le> b \<Longrightarrow> trit_not b \<le> trit_not a"
  by (cases a; cases b) auto


(* ===================================================================== *)
section \<open>Kleene Non-Complement Property\<close>
(* Unlike Boolean algebra: a AND (NOT a) != bottom for Unknown           *)
(* This is THE distinguishing axiom of K3 vs classical logic             *)
(* ===================================================================== *)

lemma kleene_not_complemented:
  "trit_and Unk (trit_not Unk) = Unk"
  unfolding trit_and_def by simp

lemma kleene_not_complemented_or:
  "trit_or Unk (trit_not Unk) = Unk"
  unfolding trit_or_def by simp


(* ===================================================================== *)
section \<open>WP4-C: Sepref Refinement Interface (Stubs)\<close>
(* Connect abstract proofs to concrete C via Sepref                      *)
(* AFP ref: "Sepref" — Stepwise Refinement for Imperative Programs       *)
(*                                                                       *)
(* Abstraction relation: nat <-> trit                                    *)
(*   0 (0b00) <-> Neg                                                    *)
(*   1 (0b01) <-> Unk                                                    *)
(*   3 (0b11) <-> Pos                                                    *)
(*   2 (0b10) <-> Fault (not in domain)                                  *)
(* ===================================================================== *)

definition trit_to_nat :: "trit \<Rightarrow> nat" where
  "trit_to_nat t = (case t of Neg \<Rightarrow> 0 | Unk \<Rightarrow> 1 | Pos \<Rightarrow> 3)"

definition nat_to_trit :: "nat \<Rightarrow> trit option" where
  "nat_to_trit n = (if n = 0 then Some Neg
                    else if n = 1 then Some Unk
                    else if n = 3 then Some Pos
                    else None)"

lemma trit_nat_roundtrip: "nat_to_trit (trit_to_nat t) = Some t"
  unfolding trit_to_nat_def nat_to_trit_def by (cases t) auto

lemma trit_nat_inj: "trit_to_nat a = trit_to_nat b \<Longrightarrow> a = b"
  unfolding trit_to_nat_def by (cases a; cases b) auto

(* Fault detection: 0b10 = 2 maps to None *)
lemma trit_fault_detection: "nat_to_trit 2 = None"
  unfolding nat_to_trit_def by simp

(* Full Sepref refinement theorem (stub — requires Isabelle-LLVM):
   (trit_and, trit2_and_impl) \<in> trit_rel \<rightarrow> trit_rel \<rightarrow> trit_rel
   where trit_rel = {(n, t). nat_to_trit n = Some t}                    *)


(* ===================================================================== *)
section \<open>WP4-C: Ternary KAT Lifting (Stubs)\<close>
(* Adapt Kleene Algebra with Tests for 3-valued guards                   *)
(* AFP ref: "KAT_and_DRA" entry                                         *)
(*                                                                       *)
(* Binary KAT axiom:  test(a) . test(not a) = 0  (complement)           *)
(* Ternary KAT weakening: test(a) . test(not a) <= Unk                  *)
(*                                                                       *)
(* Lifting strategy:                                                     *)
(*   1. Import KAT locale from AFP                                       *)
(*   2. Weaken complement axiom as above                                 *)
(*   3. Re-prove Hoare rules under weakened complement                   *)
(*   4. Show binary programs ({Neg,Pos} only) still validate             *)
(* ===================================================================== *)

lemma ternary_kat_weak_complement:
  "trit_and a (trit_not a) \<le> Unk"
  by (cases a) (auto simp: trit_and_def)

(* Binary programs satisfy the strong complement *)
lemma binary_kat_strong_complement:
  "a \<in> {Neg, Pos} \<Longrightarrow> trit_and a (trit_not a) = Neg"
  by (cases a) (auto simp: trit_and_def)

end
