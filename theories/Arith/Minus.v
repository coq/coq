(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Properties of subtraction between natural numbers.

 This file is mostly OBSOLETE now, see module [PeanoNat.Nat] instead.

 [minus] is now an alias for [Nat.sub], which is defined in [Init/Nat.v] as:
<<
Fixpoint sub (n m:nat) : nat :=
  match n, m with
  | S k, S l => k - l
  | _, _ => n
  end
where "n - m" := (sub n m) : nat_scope.
>>
*)

Require Import PeanoNat Lt Le.

Local Open Scope nat_scope.

(** * 0 is right neutral *)

Lemma minus_n_O n : n = n - 0.
Proof.
 symmetry. apply Nat.sub_0_r.
Qed.

(** * Permutation with successor *)

Lemma minus_Sn_m n m : m <= n -> S (n - m) = S n - m.
Proof.
 intros. symmetry. now apply Nat.sub_succ_l.
Qed.

Theorem pred_of_minus n : pred n = n - 1.
Proof.
 symmetry. apply Nat.sub_1_r.
Qed.

(** * Diagonal *)

Notation minus_diag := Nat.sub_diag (only parsing). (* n - n = 0 *)

Lemma minus_diag_reverse n : 0 = n - n.
Proof.
 symmetry. apply Nat.sub_diag.
Qed.

Notation minus_n_n := minus_diag_reverse.

(** * Simplification *)

Lemma minus_plus_simpl_l_reverse n m p : n - m = p + n - (p + m).
Proof.
 now rewrite Nat.sub_add_distr, Nat.add_comm, Nat.add_sub.
Qed.

(** * Relation with plus *)

Lemma plus_minus n m p : n = m + p -> p = n - m.
Proof.
 symmetry. now apply Nat.add_sub_eq_l.
Qed.

Lemma minus_plus n m : n + m - n = m.
Proof.
 rewrite Nat.add_comm. apply Nat.add_sub.
Qed.

Lemma le_plus_minus_r n m : n <= m -> n + (m - n) = m.
Proof.
 rewrite Nat.add_comm. apply Nat.sub_add.
Qed.

Lemma le_plus_minus n m : n <= m -> m = n + (m - n).
Proof.
 intros. symmetry. rewrite Nat.add_comm. now apply Nat.sub_add.
Qed.

(** * Relation with order *)

Notation minus_le_compat_r :=
  Nat.sub_le_mono_r (only parsing). (* n <= m -> n - p <= m - p. *)

Notation minus_le_compat_l :=
  Nat.sub_le_mono_l (only parsing). (* n <= m -> p - m <= p - n. *)

Notation le_minus := Nat.le_sub_l (only parsing). (* n - m <= n *)
Notation lt_minus := Nat.sub_lt (only parsing). (* m <= n -> 0 < m -> n-m < n *)

Lemma lt_O_minus_lt n m : 0 < n - m -> m < n.
Proof.
 apply Nat.lt_add_lt_sub_r.
Qed.

Theorem not_le_minus_0 n m : ~ m <= n -> n - m = 0.
Proof.
 intros. now apply Nat.sub_0_le, Nat.lt_le_incl, Nat.lt_nge.
Qed.

(** * Hints *)

Hint Resolve minus_n_O: arith.
Hint Resolve minus_Sn_m: arith.
Hint Resolve minus_diag_reverse: arith.
Hint Resolve minus_plus_simpl_l_reverse: arith.
Hint Immediate plus_minus: arith.
Hint Resolve minus_plus: arith.
Hint Resolve le_plus_minus: arith.
Hint Resolve le_plus_minus_r: arith.
Hint Resolve lt_minus: arith.
Hint Immediate lt_O_minus_lt: arith.
