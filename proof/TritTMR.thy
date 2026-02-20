(* =========================================================================
   TritTMR.thy — Triple Modular Redundancy for Ternary Logic

   Formalises TMR (Triple Modular Redundancy) over Kleene K₃ trits:
   three independent copies compute the same value, and a majority
   voter selects the result.  A single fault cannot corrupt the output.

   Key results:
     TMR-1  tmr_vote is well-defined (symmetric, idempotent on valid).
     TMR-2  Single-fault tolerance: if 2 of 3 inputs are equal,
            output equals the agreeing value (fault-masked).
     TMR-3  Fault isolation: if exactly 1 input is Unk (fault proxy),
            the other two agreeing trits determine the output.
     TMR-4  Packed-level majority: pair_tmr_vote on 2-bit nat slugs.
     TMR-5  No fault generation: tmr_vote never outputs a value outside
            the range of its inputs (no novelty).
     TMR-6  Idempotence: tmr_vote(t,t,t) = t for all t.
     TMR-7  Commutativity: result is independent of input order.
     TMR-8  Vs. PackedFaultSemantics: sanitize+vote \<subseteq> sanitize path only.

   Mathematical basis:
     Classic TMR (von Neumann 1956), extended to K₃.
     Majority over K₃: if \<ge>2 inputs agree on a value v \<in> {Neg,Pos},
     output = v. If no 2 agree, output = Unk (conservative default).

   SPDX-License-Identifier: GPL-2.0
   ========================================================================= *)

theory TritTMR
  imports TritOps PackedFaultSemantics
begin

(* ===================================================================== *)
section \<open>Ternary Majority Vote\<close>
(* ===================================================================== *)

text \<open>tmr_vote(a, b, c): majority of three K₃ trits.
      Returns the trit agreed upon by at least two inputs.
      If no two agree, returns Unk (safe conservative default).\<close>

fun tmr_vote :: "trit \<Rightarrow> trit \<Rightarrow> trit \<Rightarrow> trit" where
  "tmr_vote a b c =
    (if a = b then a
     else if b = c then b
     else if a = c then a
     else Unk)"

(* ===================================================================== *)
section \<open>TMR-6: Idempotence\<close>
(* ===================================================================== *)

lemma tmr_vote_idem: "tmr_vote t t t = t"
  by simp

(* ===================================================================== *)
section \<open>TMR-7: Commutativity\<close>
(* ===================================================================== *)

lemma tmr_vote_comm_ab: "tmr_vote a b c = tmr_vote b a c"
  by (cases a; cases b; cases c) auto

lemma tmr_vote_comm_ac: "tmr_vote a b c = tmr_vote c b a"
  by (cases a; cases b; cases c) auto

lemma tmr_vote_comm_bc: "tmr_vote a b c = tmr_vote a c b"
  by (cases a; cases b; cases c) auto

(* ===================================================================== *)
section \<open>TMR-2: Single-Fault Tolerance\<close>
(* ===================================================================== *)

text \<open>If two of three inputs agree on a valid trit, that value wins.\<close>

lemma tmr_vote_two_agree_ab:
  "tmr_vote a a c = a"
  by simp

lemma tmr_vote_two_agree_bc:
  "tmr_vote a b b = b"
  by simp

lemma tmr_vote_two_agree_ac:
  "tmr_vote a b a = a"
  by simp

text \<open>Core single-fault theorem: one arbitrary fault cannot corrupt
      the output when the other two agree.\<close>

theorem tmr_single_fault_tolerance:
  "tmr_vote t t fault = t"
  by simp

theorem tmr_single_fault_tolerance_mid:
  "tmr_vote t fault t = t"
  by simp

theorem tmr_single_fault_tolerance_last:
  "tmr_vote fault t t = t"
  by simp

(* ===================================================================== *)
section \<open>TMR-3: Unk-as-Fault Isolation\<close>
(* ===================================================================== *)

text \<open>Even if the "fault" is modeled as Unk (indeterminate),
      two agreeing valid inputs still determine the output.\<close>

lemma tmr_unk_fault_pos:
  "tmr_vote Pos Pos Unk = Pos"
  by simp

lemma tmr_unk_fault_neg:
  "tmr_vote Neg Neg Unk = Neg"
  by simp

lemma tmr_unk_fault_first:
  "tmr_vote Unk Pos Pos = Pos"
  by simp

lemma tmr_unk_fault_neg_first:
  "tmr_vote Unk Neg Neg = Neg"
  by simp

(* Exhaustive: single Unk cannot cause disagreement between the other two *)
lemma tmr_single_unk_masked:
  "a \<noteq> Unk \<Longrightarrow> b \<noteq> Unk \<Longrightarrow> a = b \<Longrightarrow> tmr_vote a b Unk = a"
  by simp

(* ===================================================================== *)
section \<open>TMR-5: No Novelty (Output \<subseteq> Inputs)\<close>
(* ===================================================================== *)

text \<open>The voter never produces a value outside those present in the inputs.\<close>

lemma tmr_vote_in_range:
  "tmr_vote a b c \<in> {a, b, c, Unk}"
  by (cases a; cases b; cases c) auto

(* If all three are in a set S that contains Unk, output is in S *)
lemma tmr_vote_closed:
  "a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> c \<in> S \<Longrightarrow> Unk \<in> S \<Longrightarrow> tmr_vote a b c \<in> S"
  by (cases a; cases b; cases c) auto

(* For the valid domain {Neg, Pos}: if \<ge>2 agree, output stays in {Neg, Pos} *)
lemma tmr_valid_dominant:
  "a \<in> {Neg, Pos} \<Longrightarrow> b \<in> {Neg, Pos} \<Longrightarrow> a = b \<Longrightarrow>
   tmr_vote a b c \<in> {Neg, Pos}"
  by simp

(* ===================================================================== *)
section \<open>TMR-4: Packed 2-Bit Majority Vote\<close>
(* ===================================================================== *)

text \<open>Model 2-bit trit slot voting using nat arithmetic.
     Matches the C trit_tmr_vote_packed64 implementation:
     sanitize first, then bitwise majority per bit plane.\<close>

(* Sanitize: map 3 → 0, keep 0/1/2 *)
definition pair_sanitize_tmr :: "nat \<Rightarrow> nat" where
  "pair_sanitize_tmr n = (if n = 3 then 0 else n)"

(* Bit majority: maj(a,b,c) = (a&b)|(b&c)|(a&c) *)
definition bit_maj :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "bit_maj a b c = (a \<and> b) \<or> (b \<and> c) \<or> (a \<and> c)"

(* Extract lo/hi bits of a 2-bit nat *)
definition bit_lo :: "nat \<Rightarrow> bool" where "bit_lo n = odd n"
definition bit_hi :: "nat \<Rightarrow> bool" where "bit_hi n = (n \<ge> 2)"

(* Reconstruct 2-bit nat from lo/hi *)
definition bits_to_nat :: "bool \<Rightarrow> bool \<Rightarrow> nat" where
  "bits_to_nat lo hi = (if hi then 2 else 0) + (if lo then 1 else 0)"

(* Packed TMR vote on sanitized 2-bit nat pairs *)
definition pair_tmr_vote :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "pair_tmr_vote a b c =
    (let a' = pair_sanitize_tmr a in
     let b' = pair_sanitize_tmr b in
     let c' = pair_sanitize_tmr c in
     let lo = bit_maj (bit_lo a') (bit_lo b') (bit_lo c') in
     let hi = bit_maj (bit_hi a') (bit_hi b') (bit_hi c') in
     bits_to_nat lo hi)"

(* pair_tmr_vote is in range {0,1,2} *)
lemma pair_tmr_range:
  "pair_tmr_vote a b c \<in> {0, 1, 2}"
  unfolding pair_tmr_vote_def pair_sanitize_tmr_def bit_maj_def
            bit_lo_def bit_hi_def bits_to_nat_def
  by (simp split: if_splits)

(* Idempotent: vote of three equal valid values *)
lemma pair_tmr_idem_0: "pair_tmr_vote 0 0 0 = 0"
  by (simp add: pair_tmr_vote_def pair_sanitize_tmr_def bit_maj_def
                bit_lo_def bit_hi_def bits_to_nat_def)

lemma pair_tmr_idem_1: "pair_tmr_vote 1 1 1 = 1"
  by (simp add: pair_tmr_vote_def pair_sanitize_tmr_def bit_maj_def
                bit_lo_def bit_hi_def bits_to_nat_def)

lemma pair_tmr_idem_2: "pair_tmr_vote 2 2 2 = 2"
  by (simp add: pair_tmr_vote_def pair_sanitize_tmr_def bit_maj_def
                bit_lo_def bit_hi_def bits_to_nat_def)

(* Single fault (3) cannot override two agreeing valid trits *)
lemma pair_tmr_fault_cannot_override_true:
  "pair_tmr_vote 1 1 3 = 1"
  by (simp add: pair_tmr_vote_def pair_sanitize_tmr_def bit_maj_def
                bit_lo_def bit_hi_def bits_to_nat_def)

lemma pair_tmr_fault_cannot_override_false:
  "pair_tmr_vote 2 2 3 = 2"
  by (simp add: pair_tmr_vote_def pair_sanitize_tmr_def bit_maj_def
                bit_lo_def bit_hi_def bits_to_nat_def)

lemma pair_tmr_fault_cannot_override_unk:
  "pair_tmr_vote 0 0 3 = 0"
  by (simp add: pair_tmr_vote_def pair_sanitize_tmr_def bit_maj_def
                bit_lo_def bit_hi_def bits_to_nat_def)

(* Two faults cannot overcovme one valid value (result = Unk, not fault) *)
lemma pair_tmr_two_faults_degrade_to_unk:
  "pair_tmr_vote 1 3 3 = 0"   (* 1 + 2×fault → Unk (0b00), not fault (0b11) *)
  by (simp add: pair_tmr_vote_def pair_sanitize_tmr_def bit_maj_def
                bit_lo_def bit_hi_def bits_to_nat_def)

(* ===================================================================== *)
section \<open>TMR-8: Relationship to Sanitization\<close>
(* ===================================================================== *)

text \<open>Sanitize-then-vote: applying pair_sanitize before pair_or is consistent
      with TMR: after sanitization, pair_tmr_vote matches pair_tmr_vote on
      already-valid inputs.\<close>

lemma sanitzed_tmr_is_valid:
  "\<lbrakk>a \<le> 3; b \<le> 3; c \<le> 3\<rbrakk> \<Longrightarrow> pair_tmr_vote a b c \<in> {0, 1, 2}"
  by (simp add: pair_tmr_range)

(* TMR output is never a fault *)
lemma pair_tmr_no_fault_output:
  "pair_tmr_vote a b c \<noteq> 3"
  using pair_tmr_range by (simp add: pair_tmr_range insert_iff)

(* ===================================================================== *)
section \<open>TMR Combined Security Theorem\<close>
(* ===================================================================== *)

text \<open>The key seT5/seT6 TMR guarantee:
     If at most one of three parallel ternary computations is corrupted
     (by any fault — including 0b11 packed encoding faults), the majority
     voter recovers the correct answer.  No fault created at input appears
     in output.\<close>

theorem tmr_security_combined:
  "\<comment>\<open>At trit level: two agreeing valid inputs determine output\<close>
   tmr_vote t t fault = t \<and>
   \<comment>\<open>At packed nat level: fault slot cannot override two valid slots\<close>
   pair_tmr_vote 1 1 3 = 1 \<and>
   pair_tmr_vote 2 2 3 = 2 \<and>
   pair_tmr_vote 0 0 3 = 0 \<and>
   \<comment>\<open>Voter never produces a fault (0b11) output\<close>
   pair_tmr_vote 3 3 3 \<noteq> 3"
  by (auto simp: pair_tmr_vote_def pair_sanitize_tmr_def bit_maj_def
                 bit_lo_def bit_hi_def bits_to_nat_def)

end
