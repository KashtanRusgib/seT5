(* -----------------------------------------------------------------------
   seT6 WP5 — Memory Isolation Proof
   
   Proves isolation properties of the seT6 memory manager:
     1. Unknown-init: freshly allocated pages contain only Unknown
     2. Scrub-on-free: freed pages are reset to Unknown
     3. No stale data: freed then re-allocated page has no prior data
     4. Page validity: ternary state machine (T=alloc, U=free, F=reserved)
     5. Owner isolation: only the owning thread can access its pages
   
   These correspond to the C implementation in:
     - src/memory.c: mem_init, mem_alloc, mem_free, mem_read, mem_write
   
   Proof method: case analysis + induction over page lifecycle.
   
   AFP basis: "Three-Valued Logic" + memory safety literature
   
   SPDX-License-Identifier: GPL-2.0
   ----------------------------------------------------------------------- *)

theory MemIsolation
  imports TritOps
begin

(* ===================================================================== *)
section \<open>Page Model\<close>
(* ===================================================================== *)

(* Page size in trits (3^6 = 729) *)
definition page_size :: nat where
  "page_size = 729"

(* A page is a fixed-length list of trits + validity + owner *)
record page =
  pg_data  :: "trit list"
  pg_valid :: trit        (* T=allocated, U=free, F=reserved *)
  pg_owner :: int         (* -1 = kernel, \<ge>0 = thread ID *)

(* Fresh page: all Unknown, validity Unknown (free), kernel-owned *)
definition page_fresh :: page where
  "page_fresh = \<lparr> pg_data = replicate page_size Unk,
                  pg_valid = Unk,
                  pg_owner = -1 \<rparr>"


(* ===================================================================== *)
section \<open>Unknown-Init Guarantee\<close>
(* Freshly allocated pages contain only Unknown trits.                   *)
(* This is THE key security property: no information leakage at alloc.   *)
(* ===================================================================== *)

(* A page is "clean" if all trits are Unknown *)
definition page_clean :: "page \<Rightarrow> bool" where
  "page_clean p = (\<forall>t \<in> set (pg_data p). t = Unk)"

(* Fresh pages are clean *)
lemma fresh_page_clean:
  "page_clean page_fresh"
  unfolding page_clean_def page_fresh_def
  by (simp add: set_replicate_conv_if page_size_def)

(* Allocation preserves cleanliness (just changes validity + owner) *)
definition page_alloc :: "page \<Rightarrow> int \<Rightarrow> page" where
  "page_alloc p owner = p\<lparr> pg_valid := Pos, pg_owner := owner \<rparr>"

lemma alloc_preserves_clean:
  "page_clean p \<Longrightarrow> page_clean (page_alloc p owner)"
  unfolding page_clean_def page_alloc_def by simp


(* ===================================================================== *)
section \<open>Scrub-on-Free Guarantee\<close>
(* Freed pages have all trits reset to Unknown.                          *)
(* This prevents information leakage between processes.                  *)
(* ===================================================================== *)

(* Free: reset data to Unknown, validity back to Unknown *)
definition page_free :: "page \<Rightarrow> page" where
  "page_free p = \<lparr> pg_data = replicate page_size Unk,
                   pg_valid = Unk,
                   pg_owner = -1 \<rparr>"

(* Freed pages are clean *)
lemma freed_page_clean:
  "page_clean (page_free p)"
  unfolding page_clean_def page_free_def
  by (simp add: set_replicate_conv_if page_size_def)

(* Free then alloc → still clean (no stale data) *)
lemma free_alloc_no_stale:
  "page_clean (page_alloc (page_free p) owner)"
  by (simp add: alloc_preserves_clean freed_page_clean)


(* ===================================================================== *)
section \<open>Page Validity State Machine\<close>
(* Valid transitions:                                                     *)
(*   Unknown (free) → Pos (allocated)   via alloc                        *)
(*   Pos (allocated) → Unknown (free)   via free                         *)
(*   Unknown (free) → Neg (reserved)    via reserve                      *)
(*   Neg (reserved): terminal (cannot be freed or allocated)              *)
(* ===================================================================== *)

(* Allocatable: only free pages *)
definition page_allocatable :: "page \<Rightarrow> bool" where
  "page_allocatable p = (pg_valid p = Unk)"

(* Freeable: only allocated pages *)
definition page_freeable :: "page \<Rightarrow> bool" where
  "page_freeable p = (pg_valid p = Pos)"

(* Reservable: only free pages *)
definition page_reservable :: "page \<Rightarrow> bool" where
  "page_reservable p = (pg_valid p = Unk)"

(* After alloc: page is allocated *)
lemma alloc_makes_allocated:
  "pg_valid (page_alloc p owner) = Pos"
  unfolding page_alloc_def by simp

(* After free: page is free *)
lemma free_makes_free:
  "pg_valid (page_free p) = Unk"
  unfolding page_free_def by simp

(* Fresh pages are allocatable *)
lemma fresh_allocatable:
  "page_allocatable page_fresh"
  unfolding page_allocatable_def page_fresh_def by simp

(* Allocated pages are not allocatable (no double-alloc) *)
lemma allocated_not_allocatable:
  "\<not> page_allocatable (page_alloc p owner)"
  unfolding page_allocatable_def page_alloc_def by simp

(* Freed pages are allocatable *)
lemma freed_allocatable:
  "page_allocatable (page_free p)"
  unfolding page_allocatable_def page_free_def by simp


(* ===================================================================== *)
section \<open>Owner Isolation\<close>
(* Only the owning thread should access its pages.                       *)
(* Access check: validity must be Pos AND requester must be owner.       *)
(* ===================================================================== *)

definition access_check :: "page \<Rightarrow> int \<Rightarrow> bool" where
  "access_check p tid = (pg_valid p = Pos \<and> pg_owner p = tid)"

(* Kernel (owner -1) can always access kernel pages *)
lemma kernel_access:
  "pg_valid p = Pos \<Longrightarrow> pg_owner p = -1 \<Longrightarrow> access_check p (-1)"
  unfolding access_check_def by simp

(* Non-owner cannot access *)
lemma non_owner_denied:
  "pg_owner p \<noteq> tid \<Longrightarrow> \<not> access_check p tid"
  unfolding access_check_def by simp

(* Free page: nobody can access *)
lemma free_no_access:
  "pg_valid p = Unk \<Longrightarrow> \<not> access_check p tid"
  unfolding access_check_def by simp

(* Reserved page: nobody can access *)
lemma reserved_no_access:
  "pg_valid p = Neg \<Longrightarrow> \<not> access_check p tid"
  unfolding access_check_def by simp


(* ===================================================================== *)
section \<open>Ternary Advantage: Uninitialized Detection\<close>
(* In binary memory, uninitialized = 0 = valid data.                     *)
(* In ternary memory, uninitialized = Unknown \<noteq> any data value.        *)
(* Reading uninitialized memory always returns a distinguishable value.   *)
(* ===================================================================== *)

(* Unknown is never confused with definite data *)
lemma uninit_distinguishable:
  "t = Unk \<Longrightarrow> t \<noteq> Pos \<and> t \<noteq> Neg"
  by auto

(* A clean page has no definite values (all Unknown) *)
lemma clean_no_definite:
  "page_clean p \<Longrightarrow> t \<in> set (pg_data p) \<Longrightarrow> t = Unk"
  unfolding page_clean_def by auto

(* Writing a value makes it definite (no longer Unknown) *)
lemma written_definite:
  "v \<noteq> Unk \<Longrightarrow> v = Pos \<or> v = Neg"
  by (cases v) auto

end
