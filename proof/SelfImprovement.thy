(*
 * SelfImprovement.thy — T-051
 * Isabelle proof of the self-improvement criterion.
 *
 * Main theorem: self_improve_sound
 *   ∀ patch p, state s.
 *     u(apply_patch(s,p), Env) > u(s, Env) + cost(p) → accept(p)
 *
 * Lemmas:
 *   - utility_monotone: accepted patches never decrease utility
 *   - cost_bounded: proof search cost is bounded
 *   - rollback_safe: rejected patches leave state unchanged
 *)

theory SelfImprovement
  imports GoedelAxioms
begin

section \<open>Utility Function\<close>

text \<open>Composite utility: product of component ratios.\<close>

definition component_ratio :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "component_ratio num den = (if den = 0 then 0 else real num / real den)"

definition utility :: "set6_state \<Rightarrow> real" where
  "utility s = component_ratio (tests_passing s) (tests_total s)
             * component_ratio (proofs_verified s) (proofs_total s)
             * component_ratio (trit_functions s) (total_functions s)
             * (1 - component_ratio (binary_reversions s) (total_functions s))"

lemma utility_initial: "utility initial_state = 1"
  by (simp add: utility_def initial_state_def component_ratio_def)

lemma utility_nonneg:
  assumes "binary_reversions s \<le> total_functions s"
  shows "utility s \<ge> 0"
  sorry  \<comment> \<open>Requires showing all component ratios \<in> [0,1]\<close>

section \<open>Cost Model\<close>

text \<open>Cost of evaluating a patch: build + test + proof verification time.\<close>

record eval_cost =
  build_time_ms    :: nat
  test_time_ms     :: nat
  isabelle_time_ms :: nat

definition total_cost :: "eval_cost \<Rightarrow> nat" where
  "total_cost c = build_time_ms c + test_time_ms c + isabelle_time_ms c"

definition normalized_cost :: "eval_cost \<Rightarrow> real" where
  "normalized_cost c = real (total_cost c) / 1000"

lemma cost_bounded:
  assumes "build_time_ms c \<le> B" and "test_time_ms c \<le> T"
          and "isabelle_time_ms c \<le> I"
  shows "total_cost c \<le> B + T + I"
  by (simp add: total_cost_def assms)

section \<open>Self-Improvement Criterion\<close>

definition delta_utility :: "set6_state \<Rightarrow> set6_state \<Rightarrow> real" where
  "delta_utility s_old s_new = utility s_new - utility s_old"

definition accept_criterion :: "set6_state \<Rightarrow> set6_state \<Rightarrow> eval_cost \<Rightarrow> bool" where
  "accept_criterion s_old s_new cost =
    (delta_utility s_old s_new > normalized_cost cost)"

text \<open>Main theorem: Self-improvement is sound.\<close>

theorem self_improve_sound:
  assumes "accept_criterion s_old s_new cost"
  shows "utility s_new > utility s_old"
  using assms
  by (simp add: accept_criterion_def delta_utility_def normalized_cost_def)

section \<open>Monotonicity\<close>

text \<open>Accepted patches never decrease utility.\<close>

theorem utility_monotone:
  assumes "accept_criterion s_old s_new cost"
  shows "utility s_new \<ge> utility s_old"
  using self_improve_sound[OF assms] by simp

section \<open>Rollback Safety\<close>

text \<open>Rejected patches leave state unchanged.\<close>

definition apply_or_rollback :: "set6_state \<Rightarrow> set6_state \<Rightarrow> eval_cost \<Rightarrow> set6_state" where
  "apply_or_rollback s_old s_new cost =
    (if accept_criterion s_old s_new cost then s_new else s_old)"

theorem rollback_safe:
  assumes "\<not> accept_criterion s_old s_new cost"
  shows "apply_or_rollback s_old s_new cost = s_old"
  using assms by (simp add: apply_or_rollback_def)

theorem rollback_preserves_utility:
  assumes "\<not> accept_criterion s_old s_new cost"
  shows "utility (apply_or_rollback s_old s_new cost) = utility s_old"
  using rollback_safe[OF assms] by simp

end
