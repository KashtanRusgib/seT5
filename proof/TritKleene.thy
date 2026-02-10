theory TritKleene
  imports Main
begin

datatype trit = Neg | Unk | Pos

(* Ordering: Neg < Unk < Pos *)
instantiation trit :: linorder
begin
fun less_eq_trit :: "trit \<Rightarrow> trit \<Rightarrow> bool" where
  "less_eq_trit Neg _ = True"
| "less_eq_trit Unk Neg = False"
| "less_eq_trit Unk _ = True"
| "less_eq_trit Pos Pos = True"
| "less_eq_trit Pos _ = False"

definition less_trit :: "trit \<Rightarrow> trit \<Rightarrow> bool" where
  "less_trit a b = (a \<le> b \<and> a \<noteq> b)"

instance proof
  fix x y z :: trit
  show "x \<le> x" by (cases x) auto
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by (cases x; cases y; cases z) auto
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" by (cases x; cases y) auto
  show "x \<le> y \<or> y \<le> x" by (cases x; cases y) auto
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" unfolding less_trit_def by (cases x; cases y) auto
qed
end

(* Kleene AND = min *)
definition trit_and :: "trit \<Rightarrow> trit \<Rightarrow> trit" where
  "trit_and a b = min a b"

(* Kleene OR = max *)
definition trit_or :: "trit \<Rightarrow> trit \<Rightarrow> trit" where
  "trit_or a b = max a b"

(* Kleene NOT *)
fun trit_not :: "trit \<Rightarrow> trit" where
  "trit_not Neg = Pos"
| "trit_not Unk = Unk"
| "trit_not Pos = Neg"

(* --- Key properties --- *)

lemma trit_and_comm: "trit_and a b = trit_and b a"
  unfolding trit_and_def by (rule min.commute)

lemma trit_and_assoc: "trit_and (trit_and a b) c = trit_and a (trit_and b c)"
  unfolding trit_and_def by (rule min.assoc)

lemma trit_or_comm: "trit_or a b = trit_or b a"
  unfolding trit_or_def by (rule max.commute)

lemma trit_not_involution: "trit_not (trit_not a) = a"
  by (cases a) auto

lemma de_morgan_and: "trit_not (trit_and a b) = trit_or (trit_not a) (trit_not b)"
  unfolding trit_and_def trit_or_def by (cases a; cases b) auto

lemma de_morgan_or: "trit_not (trit_or a b) = trit_and (trit_not a) (trit_not b)"
  unfolding trit_and_def trit_or_def by (cases a; cases b) auto

(* Unknown absorption — distinguishes Kleene from classical logic *)
lemma unknown_and_absorb: "trit_and Unk Pos = Unk"
  unfolding trit_and_def by simp

lemma unknown_or_absorb: "trit_or Unk Neg = Unk"
  unfolding trit_or_def by simp

(* Binary collapse: restricted to {Neg, Pos}, Kleene = classical *)
lemma binary_subset_and:
  "a \<in> {Neg, Pos} \<Longrightarrow> b \<in> {Neg, Pos} \<Longrightarrow>
   trit_and a b = (if a = Neg \<or> b = Neg then Neg else Pos)"
  unfolding trit_and_def by (cases a; cases b) auto

end
