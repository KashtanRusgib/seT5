(* TCAMSearch.thy — TCAM 3-Value Match Semantics
   T-036: Formal proof of TCAM search soundness and completeness.

   Theorem: ∀ key mask entry. tcam_match(key, mask, entry) ↔ 
            (∀i. mask[i]=UNKNOWN ∨ key[i]=entry[i])

   SPDX-License-Identifier: GPL-2.0 *)

theory TCAMSearch
  imports Main TernaryArith
begin

section \<open>TCAM Match Semantics\<close>

text \<open>In a ternary CAM, each cell stores True/False/Unknown.
      Unknown acts as a wildcard (don't-care) during search.\<close>

text \<open>Single-position match: a key trit matches an entry trit
      if the mask is Unknown (don't-care) or the trits are equal.\<close>

fun tcam_pos_match :: "trit \<Rightarrow> trit \<Rightarrow> trit \<Rightarrow> bool" where
  "tcam_pos_match key_t mask_t entry_t =
    (mask_t = Zero \<or> key_t = entry_t)"

text \<open>Full word match: all positions must match.\<close>

fun tcam_match :: "trit list \<Rightarrow> trit list \<Rightarrow> trit list \<Rightarrow> bool" where
  "tcam_match [] [] [] = True"
| "tcam_match (k#ks) (m#ms) (e#es) =
    (tcam_pos_match k m e \<and> tcam_match ks ms es)"
| "tcam_match _ _ _ = False"

section \<open>Soundness\<close>

text \<open>If tcam\_match returns True, then for every position i,
      either the mask is Unknown or key[i] = entry[i].\<close>

lemma tcam_match_sound:
  assumes "length key = length mask" "length mask = length entry"
          "tcam_match key mask entry"
  shows "\<forall>i < length key.
         mask ! i = Zero \<or> key ! i = entry ! i"
  using assms
  by (induction key mask entry rule: tcam_match.induct)
     (auto simp: nth_Cons split: nat.splits)

section \<open>Completeness\<close>

text \<open>If for every position the mask is Unknown or key=entry,
      then tcam\_match returns True.\<close>

lemma tcam_match_complete:
  assumes "length key = length mask" "length mask = length entry"
          "\<forall>i < length key. mask ! i = Zero \<or> key ! i = entry ! i"
  shows "tcam_match key mask entry"
  using assms
  by (induction key mask entry rule: tcam_match.induct)
     (auto, metis nth_Cons_0 nth_Cons_Suc zero_less_Suc)

section \<open>Main Theorem: Soundness + Completeness\<close>

theorem tcam_match_iff:
  assumes "length key = length mask" "length mask = length entry"
  shows "tcam_match key mask entry \<longleftrightarrow>
         (\<forall>i < length key. mask ! i = Zero \<or> key ! i = entry ! i)"
  using tcam_match_sound tcam_match_complete assms by blast

section \<open>Priority Encoding\<close>

text \<open>TCAM returns the first (highest-priority) matching entry.\<close>

fun tcam_search :: "trit list \<Rightarrow> (trit list \<times> trit list) list \<Rightarrow> nat option" where
  "tcam_search key [] = None"
| "tcam_search key ((mask, entry) # rest) =
    (if tcam_match key mask entry then Some 0
     else map_option Suc (tcam_search key rest))"

lemma tcam_search_first:
  "tcam_search key entries = Some i \<Longrightarrow>
   i < length entries \<and>
   (let (m, e) = entries ! i in tcam_match key m e) \<and>
   (\<forall>j < i. let (m, e) = entries ! j in \<not> tcam_match key m e)"
  sorry (* Structural induction on entries list — future work *)

end
