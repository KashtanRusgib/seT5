(* TernaryArith.thy — Balanced Ternary Carry-Lookahead Adder Correctness
   T-014 / T-035: Formal proof that balanced ternary addition is correct.
   
   Theorem: ∀ a b ∈ T^n. decode(ternary_add(a,b)) = decode(a) + decode(b)
   
   SPDX-License-Identifier: GPL-2.0 *)

theory TernaryArith
  imports Main "HOL-Library.Word"
begin

section \<open>Balanced Ternary Representation\<close>

text \<open>A balanced trit is an element of \{-1, 0, +1\}.\<close>

datatype trit = Neg | Zero | Pos

text \<open>Decoding a single trit to an integer.\<close>

fun trit_val :: "trit \<Rightarrow> int" where
  "trit_val Neg  = -1"
| "trit_val Zero =  0"
| "trit_val Pos  =  1"

text \<open>Decoding a balanced ternary word (LSB first) to an integer.\<close>

fun bt_decode :: "trit list \<Rightarrow> int" where
  "bt_decode []       = 0"
| "bt_decode (t # ts) = trit_val t + 3 * bt_decode ts"

section \<open>Full Adder\<close>

text \<open>Ternary full adder: takes two trits and a carry trit, 
      produces a sum trit and a carry-out trit.\<close>

fun trit_full_add :: "trit \<Rightarrow> trit \<Rightarrow> trit \<Rightarrow> trit \<times> trit" where
  "trit_full_add a b cin = (
    let s = trit_val a + trit_val b + trit_val cin in
    if s = -3 then (Zero, Neg)
    else if s = -2 then (Pos, Neg)
    else if s = -1 then (Neg, Zero)
    else if s = 0  then (Zero, Zero)
    else if s = 1  then (Pos, Zero)
    else if s = 2  then (Neg, Pos)
    else (Zero, Pos))"

section \<open>Ripple-Carry Adder\<close>

fun bt_add_carry :: "trit list \<Rightarrow> trit list \<Rightarrow> trit \<Rightarrow> trit list" where
  "bt_add_carry [] [] cin = (if cin = Zero then [] else [cin])"
| "bt_add_carry (a # as) [] cin = (
    let (s, cout) = trit_full_add a Zero cin in s # bt_add_carry as [] cout)"
| "bt_add_carry [] (b # bs) cin = (
    let (s, cout) = trit_full_add Zero b cin in s # bt_add_carry [] bs cout)"
| "bt_add_carry (a # as) (b # bs) cin = (
    let (s, cout) = trit_full_add a b cin in s # bt_add_carry as bs cout)"

definition bt_add :: "trit list \<Rightarrow> trit list \<Rightarrow> trit list" where
  "bt_add a b = bt_add_carry a b Zero"

section \<open>Correctness Theorem\<close>

text \<open>The core correctness property: decoding the sum equals 
      the sum of the decoded operands.\<close>

lemma trit_full_add_correct:
  "let (s, cout) = trit_full_add a b cin in
   trit_val s + 3 * trit_val cout = trit_val a + trit_val b + trit_val cin"
  by (cases a; cases b; cases cin; simp add: Let_def)

lemma bt_add_carry_correct:
  "bt_decode (bt_add_carry a b cin) = bt_decode a + bt_decode b + trit_val cin"
  by (induction a b cin rule: bt_add_carry.induct)
     (auto simp add: Let_def split: prod.splits,
      (metis trit_full_add_correct)+)

theorem bt_add_correct:
  "bt_decode (bt_add a b) = bt_decode a + bt_decode b"
  unfolding bt_add_def
  using bt_add_carry_correct[of a b Zero]
  by simp

section \<open>Carry Propagation Lemma\<close>

text \<open>The carry is always a valid trit (bounded in \{-1,0,+1\}).\<close>

lemma trit_full_add_carry_bounded:
  "let (_, cout) = trit_full_add a b cin in
   cout = Neg \<or> cout = Zero \<or> cout = Pos"
  by (cases a; cases b; cases cin; simp add: Let_def)

section \<open>Overflow Detection\<close>

text \<open>For n-trit words, overflow occurs if the result requires more trits.\<close>

lemma bt_add_length_bound:
  "length (bt_add a b) \<le> max (length a) (length b) + 1"
  sorry (* Requires detailed induction on carry propagation — future work *)

end
