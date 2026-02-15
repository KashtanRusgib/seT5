(* -----------------------------------------------------------------------
   seT6 WP5 — Capability Safety Proof
   
   Proves key security properties of the seT6 capability system:
     1. Monotonicity: cap_grant only narrows rights
     2. Revocation completeness: revoked caps have zero rights
     3. Validity trichotomy: cap validity is exactly {T, U, F}
     4. Access control soundness: Unknown validity → deny
   
   These correspond directly to the C implementation in:
     - src/syscall.c: kernel_cap_create, kernel_cap_grant, kernel_cap_revoke
     - src/init.c: integration tests for cap_check
   
   Proof method: case analysis on trit + set theoretic argument.
   
   AFP basis: "Three-Valued Logic" + seL4 access control formalization
   
   SPDX-License-Identifier: GPL-2.0
   ----------------------------------------------------------------------- *)

theory CapSafety
  imports TritOps
begin

(* ===================================================================== *)
section \<open>Capability Rights as Trit Sets\<close>
(* ===================================================================== *)

(* A capability right is a trit indicating permission level:
   Pos = granted, Neg = denied, Unk = pending/conditional *)

type_synonym cap_right = trit

(* Right check: conservative — only Pos grants access *)
definition cap_check :: "cap_right \<Rightarrow> bool" where
  "cap_check r = (r = Pos)"

(* Cap validity: only True (Pos) caps are active *)
definition cap_valid :: "trit \<Rightarrow> bool" where
  "cap_valid v = (v = Pos)"


(* ===================================================================== *)
section \<open>Grant Monotonicity\<close>
(* Rights can only narrow through grant (Kleene AND = intersection)     *)
(* This corresponds to: narrowed = src.rights & requested                *)
(* In Kleene logic: AND(a, b) \<le> a  and  AND(a, b) \<le> b               *)
(* ===================================================================== *)

lemma grant_narrows_left:
  "trit_and src req \<le> src"
  unfolding trit_and_def by (cases src; cases req) auto

lemma grant_narrows_right:
  "trit_and src req \<le> req"
  unfolding trit_and_def by (cases src; cases req) auto

(* Granted right is at most the source right *)
lemma grant_monotonicity:
  "cap_check (trit_and src req) \<Longrightarrow> cap_check src"
  unfolding cap_check_def trit_and_def by (cases src; cases req) auto

(* Monotonicity is transitive: chained grants only narrow further *)
lemma grant_chain_monotone:
  "trit_and (trit_and a b) c \<le> a"
proof -
  have "trit_and (trit_and a b) c \<le> trit_and a b"
    by (rule grant_narrows_left)
  also have "trit_and a b \<le> a"
    by (rule grant_narrows_left)
  finally show ?thesis .
qed


(* ===================================================================== *)
section \<open>Revocation Completeness\<close>
(* After revocation: rights = Neg (bottom), valid = Neg                  *)
(* ===================================================================== *)

(* Revoked cap has no rights *)
lemma revoked_no_access:
  "\<not> cap_check Neg"
  unfolding cap_check_def by simp

(* Revoked cap is invalid *)
lemma revoked_invalid:
  "\<not> cap_valid Neg"
  unfolding cap_valid_def by simp

(* Unknown cap is also denied (conservative) *)
lemma unknown_denied:
  "\<not> cap_check Unk"
  unfolding cap_check_def by simp

lemma unknown_invalid:
  "\<not> cap_valid Unk"
  unfolding cap_valid_def by simp


(* ===================================================================== *)
section \<open>Validity Trichotomy\<close>
(* Every cap is exactly one of: active (Pos), pending (Unk), revoked (Neg) *)
(* ===================================================================== *)

lemma validity_trichotomy:
  "v = Neg \<or> v = Unk \<or> v = Pos"
  by (cases v) auto

lemma valid_means_pos:
  "cap_valid v \<Longrightarrow> v = Pos"
  unfolding cap_valid_def by auto


(* ===================================================================== *)
section \<open>Access Control Soundness\<close>
(* If access is granted, both validity and right must be Pos              *)
(* ===================================================================== *)

definition access_allowed :: "trit \<Rightarrow> cap_right \<Rightarrow> bool" where
  "access_allowed validity right = (cap_valid validity \<and> cap_check right)"

lemma access_requires_valid:
  "access_allowed v r \<Longrightarrow> v = Pos"
  unfolding access_allowed_def cap_valid_def by auto

lemma access_requires_right:
  "access_allowed v r \<Longrightarrow> r = Pos"
  unfolding access_allowed_def cap_check_def by auto

(* Unknown anywhere in the chain → denied *)
lemma unknown_blocks_access:
  "v = Unk \<or> r = Unk \<Longrightarrow> \<not> access_allowed v r"
  unfolding access_allowed_def cap_valid_def cap_check_def by auto

(* Neg anywhere → denied *)
lemma neg_blocks_access:
  "v = Neg \<or> r = Neg \<Longrightarrow> \<not> access_allowed v r"
  unfolding access_allowed_def cap_valid_def cap_check_def by auto


(* ===================================================================== *)
section \<open>Ternary Advantage: Unknown Propagation in Caps\<close>
(* This is what makes ternary caps strictly more secure than binary.    *)
(* Binary: uninitialized cap = 0 = valid integer, potentially confused. *)
(* Ternary: uninitialized cap = Unknown, which is automatically denied. *)
(* ===================================================================== *)

lemma uninitialized_denied:
  "\<not> access_allowed Unk Unk"
  unfolding access_allowed_def cap_valid_def cap_check_def by simp

(* Even if right is granted, unknown validity blocks *)
lemma unknown_validity_blocks:
  "\<not> access_allowed Unk Pos"
  unfolding access_allowed_def cap_valid_def by simp

(* Even if validity is confirmed, unknown right blocks *)
lemma unknown_right_blocks:
  "\<not> access_allowed Pos Unk"
  unfolding access_allowed_def cap_check_def by simp

end
