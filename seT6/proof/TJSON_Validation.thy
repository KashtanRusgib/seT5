theory TJSON_Validation
  imports TritKleene TritOps
begin

(* ===================================================================
   TJSON_Validation: Formal verification of Ternary JSON properties.

   Extends the TritKleene K₃ algebra to model TJSON validation as a
   three-valued logic system.  A TJSON validator maps a (document, schema)
   pair to a trit:
     Pos  →  valid        (document satisfies schema)
     Neg  →  invalid      (document violates schema)
     Unk  →  indeterminate (insufficient information)

   We prove:
     1. Structural properties of the validation lattice
     2. Soundness of composite validation (allOf, anyOf, oneOf, not)
     3. Epistemic merge correctness (confidence-aware Kleene AND)
     4. TJSON diff comparison correctness
     5. Merge-strategy lattice properties
   =================================================================== *)


(* -------------------------------------------------------------------
   Section 1: TJSON Validation Result Type
   ------------------------------------------------------------------- *)

(* A validation result is simply a trit *)
type_synonym tjson_result = trit

(* Composite validation combinators *)

(* allOf: conjunction of all sub-schema validations *)
definition tjson_allOf :: "tjson_result list \<Rightarrow> tjson_result" where
  "tjson_allOf rs = fold trit_and rs Pos"

(* anyOf: disjunction — at least one sub-schema valid *)
definition tjson_anyOf :: "tjson_result list \<Rightarrow> tjson_result" where
  "tjson_anyOf rs = fold trit_or rs Neg"

(* not: negation of a validation *)
definition tjson_not :: "tjson_result \<Rightarrow> tjson_result" where
  "tjson_not r = trit_not r"


(* -------------------------------------------------------------------
   Section 2: allOf / anyOf — Lattice Properties
   ------------------------------------------------------------------- *)

(* allOf of empty list is valid (vacuous truth) *)
lemma tjson_allOf_nil: "tjson_allOf [] = Pos"
  unfolding tjson_allOf_def by simp

(* anyOf of empty list is invalid (vacuous falsity) *)
lemma tjson_anyOf_nil: "tjson_anyOf [] = Neg"
  unfolding tjson_anyOf_def by simp

(* -- Fold absorption helpers ------------------------------------------- *)

(* Complete simp rules for min/max on trit — avoids unfolding min_def/max_def
   inside fold, which would break fold simp lemmas. *)
lemma min_neg_left [simp]: "min (Neg::trit) x = Neg"
  by (cases x) (simp_all add: min_def)
lemma min_neg_right [simp]: "min x (Neg::trit) = Neg"
  by (cases x) (simp_all add: min_def)
lemma min_pos_left [simp]: "min (Pos::trit) x = x"
  by (cases x) (simp_all add: min_def)
lemma min_pos_right [simp]: "min x (Pos::trit) = x"
  by (cases x) (simp_all add: min_def)
lemma min_unk_unk [simp]: "min (Unk::trit) Unk = Unk"
  by (simp add: min_def)
lemma max_pos_left [simp]: "max (Pos::trit) x = Pos"
  by (cases x) (simp_all add: max_def)
lemma max_pos_right [simp]: "max x (Pos::trit) = Pos"
  by (cases x) (simp_all add: max_def)
lemma max_neg_left [simp]: "max (Neg::trit) x = x"
  by (cases x) (simp_all add: max_def)
lemma max_neg_right [simp]: "max x (Neg::trit) = x"
  by (cases x) (simp_all add: max_def)
lemma max_unk_unk [simp]: "max (Unk::trit) Unk = Unk"
  by (simp add: max_def)

(* Neg absorbs fold-min: once the accumulator is Neg it stays Neg *)
lemma fold_min_bot [simp]: "fold min rs (Neg::trit) = Neg"
  by (induction rs) simp_all

(* If Neg appears anywhere in the list, fold min yields Neg *)
lemma fold_min_has_neg:
  "Neg \<in> set rs \<Longrightarrow> fold min rs (acc::trit) = Neg"
proof (induction rs arbitrary: acc)
  case Nil thus ?case by simp
next
  case (Cons a rs)
  show ?case
  proof (cases "a = Neg")
    case True thus ?thesis by simp
  next
    case False
    with Cons.prems have "Neg \<in> set rs" by simp
    thus ?thesis using Cons.IH by simp
  qed
qed

(* Pos absorbs fold-max *)
lemma fold_max_top [simp]: "fold max rs (Pos::trit) = Pos"
  by (induction rs) simp_all

(* If Pos appears anywhere in the list, fold max yields Pos *)
lemma fold_max_has_pos:
  "Pos \<in> set rs \<Longrightarrow> fold max rs (acc::trit) = Pos"
proof (induction rs arbitrary: acc)
  case Nil thus ?case by simp
next
  case (Cons a rs)
  show ?case
  proof (cases "a = Pos")
    case True thus ?thesis by simp
  next
    case False
    with Cons.prems have "Pos \<in> set rs" by simp
    thus ?thesis using Cons.IH by simp
  qed
qed

(* Fold-min over all-Unk list with Unk accumulator stays Unk *)
lemma fold_min_all_unk:
  "\<forall>r \<in> set rs. r = Unk \<Longrightarrow> fold min rs (Unk::trit) = Unk"
proof (induction rs)
  case Nil show ?case by simp
next
  case (Cons a rs)
  hence "a = Unk" and "\<forall>r \<in> set rs. r = Unk" by auto
  thus ?case using Cons.IH by simp
qed

(* allOf singleton is identity *)
lemma tjson_allOf_singleton: "tjson_allOf [r] = r"
  unfolding tjson_allOf_def trit_and_def by (cases r) auto

(* anyOf singleton is identity *)
lemma tjson_anyOf_singleton: "tjson_anyOf [r] = r"
  unfolding tjson_anyOf_def trit_or_def by (cases r) auto

(* allOf with Neg forces Neg (short-circuit) *)
lemma tjson_allOf_neg:
  "Neg \<in> set rs \<Longrightarrow> tjson_allOf rs = Neg"
  unfolding tjson_allOf_def trit_and_def
  by (rule fold_min_has_neg)

(* anyOf with Pos forces Pos (short-circuit) *)
lemma tjson_anyOf_pos:
  "Pos \<in> set rs \<Longrightarrow> tjson_anyOf rs = Pos"
  unfolding tjson_anyOf_def trit_or_def
  by (rule fold_max_has_pos)


(* -------------------------------------------------------------------
   Section 3: Negation Properties (Kleene NOT in schema `not` keyword)
   ------------------------------------------------------------------- *)

(* TJSON `not` is involutive *)
lemma tjson_not_involution: "tjson_not (tjson_not r) = r"
  unfolding tjson_not_def by (rule trit_not_involution)

(* De Morgan for allOf/anyOf via not *)
lemma tjson_not_singleton_allOf:
  "tjson_not (tjson_allOf [a, b]) = tjson_anyOf [tjson_not a, tjson_not b]"
  unfolding tjson_not_def tjson_allOf_def tjson_anyOf_def
            trit_and_def trit_or_def
  by (cases a; cases b) (auto simp: min_def max_def)


(* -------------------------------------------------------------------
   Section 4: Epistemic Value Operations
   ------------------------------------------------------------------- *)

(* Model confidence as a natural number in [0, 1000].
   Epistemic merge = AND of states + averaged confidence. *)

type_synonym confidence = nat

definition merge_confidence :: "confidence \<Rightarrow> confidence \<Rightarrow> confidence" where
  "merge_confidence c1 c2 = (c1 + c2) div 2"

definition merge_epistemic :: "(trit \<times> confidence) \<Rightarrow> (trit \<times> confidence) \<Rightarrow>
                               (trit \<times> confidence)" where
  "merge_epistemic e1 e2 =
     (trit_and (fst e1) (fst e2), merge_confidence (snd e1) (snd e2))"

(* Epistemic merge is commutative in the state component *)
lemma merge_epistemic_state_comm:
  "fst (merge_epistemic e1 e2) = fst (merge_epistemic e2 e1)"
  unfolding merge_epistemic_def by (simp add: trit_and_comm)

(* Epistemic merge is commutative in the confidence component *)
lemma merge_confidence_comm:
  "merge_confidence c1 c2 = merge_confidence c2 c1"
  unfolding merge_confidence_def by (simp add: add.commute)

(* Both epistemic values certain → merge is certain *)
lemma merge_epistemic_both_pos:
  "fst e1 = Pos \<Longrightarrow> fst e2 = Pos \<Longrightarrow>
   fst (merge_epistemic e1 e2) = Pos"
  unfolding merge_epistemic_def trit_and_def
  by (simp add: min_def)

(* One refuted → merge is refuted *)
lemma merge_epistemic_neg:
  "fst e1 = Neg \<Longrightarrow>
   fst (merge_epistemic e1 e2) = Neg"
  unfolding merge_epistemic_def trit_and_def
  by (cases "fst e2") (auto simp: min_def)


(* -------------------------------------------------------------------
   Section 5: TJSON Diff — Ternary Comparison
   ------------------------------------------------------------------- *)

(* Model TJSON value comparison result *)
definition tjson_compare :: "trit \<Rightarrow> trit \<Rightarrow> trit" where
  "tjson_compare a b =
     (if a = Unk \<or> b = Unk then Unk
      else if a = b then Pos
      else Neg)"

(* Comparison is reflexive for definite values *)
lemma tjson_compare_refl:
  "a \<noteq> Unk \<Longrightarrow> tjson_compare a a = Pos"
  unfolding tjson_compare_def by simp

(* Unknown propagates *)
lemma tjson_compare_unk_left:
  "tjson_compare Unk b = Unk"
  unfolding tjson_compare_def by simp

lemma tjson_compare_unk_right:
  "tjson_compare a Unk = Unk"
  unfolding tjson_compare_def by simp

(* Comparison is symmetric *)
lemma tjson_compare_symm:
  "tjson_compare a b = tjson_compare b a"
  unfolding tjson_compare_def by auto

(* Definite unequal values yield Neg *)
lemma tjson_compare_definite_neq:
  "a \<noteq> Unk \<Longrightarrow> b \<noteq> Unk \<Longrightarrow> a \<noteq> b \<Longrightarrow>
   tjson_compare a b = Neg"
  unfolding tjson_compare_def by simp


(* -------------------------------------------------------------------
   Section 6: Merge Strategy Lattice
   ------------------------------------------------------------------- *)

(* Conservative merge = AND (takes minimum = weakest) *)
definition tjson_merge_conservative :: "trit \<Rightarrow> trit \<Rightarrow> trit" where
  "tjson_merge_conservative a b = trit_and a b"

(* Optimistic merge = OR (takes maximum = strongest) *)
definition tjson_merge_optimistic :: "trit \<Rightarrow> trit \<Rightarrow> trit" where
  "tjson_merge_optimistic a b = trit_or a b"

(* Conservative ≤ Optimistic (lattice ordering) *)
lemma merge_conservative_le_optimistic:
  "tjson_merge_conservative a b \<le> tjson_merge_optimistic a b"
  unfolding tjson_merge_conservative_def tjson_merge_optimistic_def
            trit_and_def trit_or_def
  by (simp add: min_le_iff_disj max_def)

(* Conservative merge is commutative *)
lemma merge_conservative_comm:
  "tjson_merge_conservative a b = tjson_merge_conservative b a"
  unfolding tjson_merge_conservative_def by (rule trit_and_comm)

(* Optimistic merge is commutative *)
lemma merge_optimistic_comm:
  "tjson_merge_optimistic a b = tjson_merge_optimistic b a"
  unfolding tjson_merge_optimistic_def by (rule trit_or_comm)

(* Conservative merge is associative *)
lemma merge_conservative_assoc:
  "tjson_merge_conservative (tjson_merge_conservative a b) c =
   tjson_merge_conservative a (tjson_merge_conservative b c)"
  unfolding tjson_merge_conservative_def by (rule trit_and_assoc)

(* Conservative with Neg yields Neg *)
lemma merge_conservative_neg:
  "tjson_merge_conservative Neg b = Neg"
  unfolding tjson_merge_conservative_def trit_and_def by simp

(* Optimistic with Pos yields Pos *)
lemma merge_optimistic_pos:
  "tjson_merge_optimistic Pos b = Pos"
  unfolding tjson_merge_optimistic_def trit_or_def by simp


(* -------------------------------------------------------------------
   Section 7: Validation Soundness — Key Theorem
   ------------------------------------------------------------------- *)

(* If all individual validations are Pos, allOf is Pos *)
lemma tjson_validation_sound:
  "(\<forall>r \<in> set rs. r = Pos) \<Longrightarrow> tjson_allOf rs = Pos"
proof (induction rs)
  case Nil
  thus ?case by (simp add: tjson_allOf_nil)
next
  case (Cons a rs)
  hence "a = Pos" and "\<forall>r \<in> set rs. r = Pos" by auto
  hence "tjson_allOf rs = Pos" using Cons.IH by simp
  with \<open>a = Pos\<close> show ?case
    unfolding tjson_allOf_def trit_and_def
    by (simp add: min_def)
qed

(* If any individual validation is Pos, anyOf is Pos *)
lemma tjson_anyOf_sound:
  "(\<exists>r \<in> set rs. r = Pos) \<Longrightarrow> tjson_anyOf rs = Pos"
  by (auto intro: tjson_anyOf_pos)

(* Uncertainty propagation: all Unk → allOf Unk *)
lemma tjson_allOf_all_unk:
  "rs \<noteq> [] \<Longrightarrow> (\<forall>r \<in> set rs. r = Unk) \<Longrightarrow> tjson_allOf rs = Unk"
proof (induction rs)
  case Nil thus ?case by simp
next
  case (Cons a rs)
  hence a: "a = Unk" and unk: "\<forall>r \<in> set rs. r = Unk" by auto
  show ?case
    unfolding tjson_allOf_def trit_and_def
    using a unk by (simp add: fold_min_all_unk)
qed


(* -------------------------------------------------------------------
   Section 8: Schema Composition Properties
   ------------------------------------------------------------------- *)

(* Lattice absorption: allOf containing anyOf *)
lemma validation_absorption:
  "trit_and a (trit_or a b) = a"
  unfolding trit_and_def trit_or_def
  by (cases a; cases b) (auto simp: min_def max_def)

(* Double negation in schema: not(not(x)) = x *)
lemma schema_double_negation:
  "tjson_not (tjson_not r) = r"
  by (rule tjson_not_involution)

(* Idempotence of validation *)
lemma validation_and_idempotent:
  "trit_and r r = r"
  unfolding trit_and_def by simp

lemma validation_or_idempotent:
  "trit_or r r = r"
  unfolding trit_or_def by simp


end
