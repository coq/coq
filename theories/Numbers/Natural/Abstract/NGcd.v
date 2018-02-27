(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Properties of the greatest common divisor *)

Require Import NAxioms NSub NZGcd.

Module Type NGcdProp
 (Import A : NAxiomsSig')
 (Import B : NSubProp A).

 Include NZGcdProp A A B.

(** Results concerning divisibility*)

Definition divide_1_r n : (n | 1) -> n == 1
 := divide_1_r_nonneg n (le_0_l n).

Definition divide_antisym n m : (n | m) -> (m | n) -> n == m
 := divide_antisym_nonneg n m (le_0_l n) (le_0_l m).

Lemma divide_add_cancel_r : forall n m p, (n | m) -> (n | m + p) -> (n | p).
Proof.
 intros n m p (q,Hq) (r,Hr).
 exists (r-q). rewrite mul_sub_distr_r, <- Hq, <- Hr.
 now rewrite add_comm, add_sub.
Qed.

Lemma divide_sub_r : forall n m p, (n | m) -> (n | p) -> (n | m - p).
Proof.
 intros n m p H H'.
 destruct (le_ge_cases m p) as [LE|LE].
 apply sub_0_le in LE. rewrite LE. apply divide_0_r.
 apply divide_add_cancel_r with p; trivial.
 now rewrite add_comm, sub_add.
Qed.

(** Properties of gcd *)

Definition gcd_0_l n : gcd 0 n == n := gcd_0_l_nonneg n (le_0_l n).
Definition gcd_0_r n : gcd n 0 == n := gcd_0_r_nonneg n (le_0_l n).
Definition gcd_diag n : gcd n n == n := gcd_diag_nonneg n (le_0_l n).
Definition gcd_unique' n m p := gcd_unique n m p (le_0_l p).
Definition gcd_unique_alt' n m p := gcd_unique_alt n m p (le_0_l p).
Definition divide_gcd_iff' n m := divide_gcd_iff n m (le_0_l n).

Lemma gcd_add_mult_diag_r : forall n m p, gcd n (m+p*n) == gcd n m.
Proof.
 intros. apply gcd_unique_alt'.
 intros. rewrite gcd_divide_iff. split; intros (U,V); split; trivial.
 apply divide_add_r; trivial. now apply divide_mul_r.
 apply divide_add_cancel_r with (p*n); trivial.
 now apply divide_mul_r. now rewrite add_comm.
Qed.

Lemma gcd_add_diag_r : forall n m, gcd n (m+n) == gcd n m.
Proof.
 intros n m. rewrite <- (mul_1_l n) at 2. apply gcd_add_mult_diag_r.
Qed.

Lemma gcd_sub_diag_r : forall n m, n<=m -> gcd n (m-n) == gcd n m.
Proof.
 intros n m H. symmetry.
 rewrite <- (sub_add n m H) at 1. apply gcd_add_diag_r.
Qed.

(** On natural numbers, we should use a particular form
  for the Bezout identity, since we don't have full subtraction. *)

Definition Bezout n m p := exists a b, a*n == p + b*m.

Instance Bezout_wd : Proper (eq==>eq==>eq==>iff) Bezout.
Proof.
 unfold Bezout. intros x x' Hx y y' Hy z z' Hz.
 setoid_rewrite Hx. setoid_rewrite Hy. now setoid_rewrite Hz.
Qed.

Lemma bezout_1_gcd : forall n m, Bezout n m 1 -> gcd n m == 1.
Proof.
 intros n m (q & r & H).
 apply gcd_unique; trivial using divide_1_l, le_0_1.
 intros p Hn Hm.
 apply divide_add_cancel_r with (r*m).
 now apply divide_mul_r.
 rewrite add_comm, <- H. now apply divide_mul_r.
Qed.

(** For strictly positive numbers, we have Bezout in the two directions. *)

Lemma gcd_bezout_pos_pos : forall n, 0<n -> forall m, 0<m ->
 Bezout n m (gcd n m) /\ Bezout m n (gcd n m).
Proof.
 intros n Hn. rewrite <- le_succ_l, <- one_succ in Hn.
 pattern n. apply strong_right_induction with (z:=1); trivial.
 unfold Bezout. solve_proper.
 clear n Hn. intros n Hn IHn.
 intros m Hm. rewrite <- le_succ_l, <- one_succ in Hm.
 pattern m. apply strong_right_induction with (z:=1); trivial.
 unfold Bezout. solve_proper.
 clear m Hm. intros m Hm IHm.
 destruct (lt_trichotomy n m) as [LT|[EQ|LT]].
 (* n < m *)
 destruct (IHm (m-n)) as ((a & b & EQ), (a' & b' & EQ')).
 rewrite one_succ, le_succ_l.
 apply lt_add_lt_sub_l; now nzsimpl.
 apply sub_lt; order'.
 split.
 exists (a+b). exists b.
 rewrite mul_add_distr_r, EQ, mul_sub_distr_l, <- add_assoc.
 rewrite gcd_sub_diag_r by order.
 rewrite sub_add. reflexivity. apply mul_le_mono_l; order.
 exists a'. exists (a'+b').
 rewrite gcd_sub_diag_r in EQ' by order.
 rewrite (add_comm a'), mul_add_distr_r, add_assoc, <- EQ'.
 rewrite mul_sub_distr_l, sub_add. reflexivity. apply mul_le_mono_l; order.
 (* n = m *)
 rewrite EQ. rewrite gcd_diag.
 split.
 exists 1. exists 0. now nzsimpl.
 exists 1. exists 0. now nzsimpl.
 (* m < n *)
 rewrite gcd_comm, and_comm.
 apply IHn; trivial.
 now rewrite <- le_succ_l, <- one_succ.
Qed.

Lemma gcd_bezout_pos : forall n m, 0<n -> Bezout n m (gcd n m).
Proof.
 intros n m Hn.
 destruct (eq_0_gt_0_cases m) as [EQ|LT].
 rewrite EQ, gcd_0_r. exists 1. exists 0. now nzsimpl.
 now apply gcd_bezout_pos_pos.
Qed.

(** For arbitrary natural numbers, we could only say that at least
  one of the Bezout identities holds. *)

Lemma gcd_bezout : forall n m,
 Bezout n m (gcd n m) \/ Bezout m n (gcd n m).
Proof.
 intros n m.
 destruct (eq_0_gt_0_cases n) as [EQ|LT].
 right. rewrite EQ, gcd_0_l. exists 1. exists 0. now nzsimpl.
 left. now apply gcd_bezout_pos.
Qed.

Lemma gcd_mul_mono_l :
  forall n m p, gcd (p * n) (p * m) == p * gcd n m.
Proof.
 intros n m p.
 apply gcd_unique'.
 apply mul_divide_mono_l, gcd_divide_l.
 apply mul_divide_mono_l, gcd_divide_r.
 intros q H H'.
 destruct (eq_0_gt_0_cases n) as [EQ|LT].
 rewrite EQ in *. now rewrite gcd_0_l.
 destruct (gcd_bezout_pos n m) as (a & b & EQ); trivial.
 apply divide_add_cancel_r with (p*m*b).
 now apply divide_mul_l.
 rewrite <- mul_assoc, <- mul_add_distr_l, add_comm, (mul_comm m), <- EQ.
 rewrite (mul_comm a), mul_assoc.
 now apply divide_mul_l.
Qed.

Lemma gcd_mul_mono_r :
 forall n m p, gcd (n*p) (m*p) == gcd n m * p.
Proof.
 intros. rewrite !(mul_comm _ p). apply gcd_mul_mono_l.
Qed.

Lemma gauss : forall n m p, (n | m * p) -> gcd n m == 1 -> (n | p).
Proof.
 intros n m p H G.
 destruct (eq_0_gt_0_cases n) as [EQ|LT].
 rewrite EQ in *. rewrite gcd_0_l in G. now rewrite <- (mul_1_l p), <- G.
 destruct (gcd_bezout_pos n m) as (a & b & EQ); trivial.
 rewrite G in EQ.
 apply divide_add_cancel_r with (m*p*b).
 now apply divide_mul_l.
 rewrite (mul_comm _ b), mul_assoc. rewrite <- (mul_1_l p) at 2.
 rewrite <- mul_add_distr_r, add_comm, <- EQ.
 now apply divide_mul_l, divide_factor_r.
Qed.

Lemma divide_mul_split : forall n m p, n ~= 0 -> (n | m * p) ->
 exists q r, n == q*r /\ (q | m) /\ (r | p).
Proof.
 intros n m p Hn H.
 assert (G := gcd_nonneg n m). le_elim G.
 destruct (gcd_divide_l n m) as (q,Hq).
 exists (gcd n m). exists q.
 split. now rewrite mul_comm.
 split. apply gcd_divide_r.
 destruct (gcd_divide_r n m) as (r,Hr).
 rewrite Hr in H. rewrite Hq in H at 1.
 rewrite mul_shuffle0 in H. apply mul_divide_cancel_r in H; [|order].
 apply gauss with r; trivial.
 apply mul_cancel_r with (gcd n m); [order|].
 rewrite mul_1_l.
 rewrite <- gcd_mul_mono_r, <- Hq, <- Hr; order.
 symmetry in G. apply gcd_eq_0 in G. destruct G as (Hn',_); order.
Qed.

(** TODO : relation between gcd and division and modulo *)

(** TODO : more about rel_prime (i.e. gcd == 1), about prime ... *)

End NGcdProp.
