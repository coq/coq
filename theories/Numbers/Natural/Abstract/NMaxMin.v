(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import NAxioms NSub GenericMinMax.

(** * Properties of minimum and maximum specific to natural numbers *)

Module Type NMaxMinProp (Import N : NAxiomsMiniSig').
Include NSubProp N.

(** Zero *)

Lemma max_0_l : forall n, max 0 n == n.
Proof.
 intros. apply max_r. apply le_0_l.
Qed.

Lemma max_0_r : forall n, max n 0 == n.
Proof.
 intros. apply max_l. apply le_0_l.
Qed.

Lemma min_0_l : forall n, min 0 n == 0.
Proof.
 intros. apply min_l. apply le_0_l.
Qed.

Lemma min_0_r : forall n, min n 0 == 0.
Proof.
 intros. apply min_r. apply le_0_l.
Qed.

(** The following results are concrete instances of [max_monotone]
    and similar lemmas. *)

(** Succ *)

Lemma succ_max_distr : forall n m, S (max n m) == max (S n) (S m).
Proof.
 intros. destruct (le_ge_cases n m);
  [rewrite 2 max_r | rewrite 2 max_l]; now rewrite <- ?succ_le_mono.
Qed.

Lemma succ_min_distr : forall n m, S (min n m) == min (S n) (S m).
Proof.
 intros. destruct (le_ge_cases n m);
  [rewrite 2 min_l | rewrite 2 min_r]; now rewrite <- ?succ_le_mono.
Qed.

(** Add *)

Lemma add_max_distr_l : forall n m p, max (p + n) (p + m) == p + max n m.
Proof.
 intros. destruct (le_ge_cases n m);
  [rewrite 2 max_r | rewrite 2 max_l]; now rewrite <- ?add_le_mono_l.
Qed.

Lemma add_max_distr_r : forall n m p, max (n + p) (m + p) == max n m + p.
Proof.
 intros. destruct (le_ge_cases n m);
  [rewrite 2 max_r | rewrite 2 max_l]; now rewrite <- ?add_le_mono_r.
Qed.

Lemma add_min_distr_l : forall n m p, min (p + n) (p + m) == p + min n m.
Proof.
 intros. destruct (le_ge_cases n m);
  [rewrite 2 min_l | rewrite 2 min_r]; now rewrite <- ?add_le_mono_l.
Qed.

Lemma add_min_distr_r : forall n m p, min (n + p) (m + p) == min n m + p.
Proof.
 intros. destruct (le_ge_cases n m);
  [rewrite 2 min_l | rewrite 2 min_r]; now rewrite <- ?add_le_mono_r.
Qed.

(** Mul *)

Lemma mul_max_distr_l : forall n m p, max (p * n) (p * m) == p * max n m.
Proof.
 intros. destruct (le_ge_cases n m);
  [rewrite 2 max_r | rewrite 2 max_l]; try order; now apply mul_le_mono_l.
Qed.

Lemma mul_max_distr_r : forall n m p, max (n * p) (m * p) == max n m * p.
Proof.
 intros. destruct (le_ge_cases n m);
  [rewrite 2 max_r | rewrite 2 max_l]; try order; now apply mul_le_mono_r.
Qed.

Lemma mul_min_distr_l : forall n m p, min (p * n) (p * m) == p * min n m.
Proof.
 intros. destruct (le_ge_cases n m);
  [rewrite 2 min_l | rewrite 2 min_r]; try order; now apply mul_le_mono_l.
Qed.

Lemma mul_min_distr_r : forall n m p, min (n * p) (m * p) == min n m * p.
Proof.
 intros. destruct (le_ge_cases n m);
  [rewrite 2 min_l | rewrite 2 min_r]; try order; now apply mul_le_mono_r.
Qed.

(** Sub *)

Lemma sub_max_distr_l : forall n m p, max (p - n) (p - m) == p - min n m.
Proof.
 intros. destruct (le_ge_cases n m).
 rewrite min_l by trivial. apply max_l. now apply sub_le_mono_l.
 rewrite min_r by trivial. apply max_r. now apply sub_le_mono_l.
Qed.

Lemma sub_max_distr_r : forall n m p, max (n - p) (m - p) == max n m - p.
Proof.
 intros. destruct (le_ge_cases n m);
  [rewrite 2 max_r | rewrite 2 max_l]; try order; now apply sub_le_mono_r.
Qed.

Lemma sub_min_distr_l : forall n m p, min (p - n) (p - m) == p - max n m.
Proof.
 intros. destruct (le_ge_cases n m).
 rewrite max_r by trivial. apply min_r. now apply sub_le_mono_l.
 rewrite max_l by trivial. apply min_l. now apply sub_le_mono_l.
Qed.

Lemma sub_min_distr_r : forall n m p, min (n - p) (m - p) == min n m - p.
Proof.
 intros. destruct (le_ge_cases n m);
  [rewrite 2 min_l | rewrite 2 min_r]; try order; now apply sub_le_mono_r.
Qed.

End NMaxMinProp.
