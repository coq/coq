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

Require Import ZAxioms ZMulOrder ZSgnAbs NZGcd.

Module Type ZGcdProp
 (Import A : ZAxiomsSig')
 (Import B : ZMulOrderProp A)
 (Import C : ZSgnAbsProp A B).

 Include NZGcdProp A A B.

(** Results concerning divisibility*)

Lemma divide_opp_l : forall n m, (-n | m) <-> (n | m).
Proof.
 intros n m. split; intros (p,Hp); exists (-p); rewrite Hp.
  now rewrite mul_opp_l, mul_opp_r.
  now rewrite mul_opp_opp.
Qed.

Lemma divide_opp_r : forall n m, (n | -m) <-> (n | m).
Proof.
 intros n m. split; intros (p,Hp); exists (-p).
  now rewrite mul_opp_l, <- Hp, opp_involutive.
  now rewrite Hp, mul_opp_l.
Qed.

Lemma divide_abs_l : forall n m, (abs n | m) <-> (n | m).
Proof.
 intros n m. destruct (abs_eq_or_opp n) as [H|H]; rewrite H.
 easy. apply divide_opp_l.
Qed.

Lemma divide_abs_r : forall n m, (n | abs m) <-> (n | m).
Proof.
 intros n m. destruct (abs_eq_or_opp m) as [H|H]; rewrite H.
 easy. apply divide_opp_r.
Qed.

Lemma divide_1_r_abs : forall n, (n | 1) -> abs n == 1.
Proof.
 intros n Hn. apply divide_1_r_nonneg. apply abs_nonneg.
 now apply divide_abs_l.
Qed.

Lemma divide_1_r : forall n, (n | 1) -> n==1 \/ n==-1.
Proof.
 intros n (m,H). rewrite mul_comm in H. now apply eq_mul_1 with m.
Qed.

Lemma divide_antisym_abs : forall n m,
 (n | m) -> (m | n) -> abs n == abs m.
Proof.
 intros. apply divide_antisym_nonneg; try apply abs_nonneg.
 now apply divide_abs_l, divide_abs_r.
 now apply divide_abs_l, divide_abs_r.
Qed.

Lemma divide_antisym : forall n m,
 (n | m) -> (m | n) -> n == m \/ n == -m.
Proof.
 intros. now apply abs_eq_cases, divide_antisym_abs.
Qed.

Lemma divide_sub_r : forall n m p, (n | m) -> (n | p) -> (n | m - p).
Proof.
 intros n m p H H'. rewrite <- add_opp_r.
 apply divide_add_r; trivial. now apply divide_opp_r.
Qed.

Lemma divide_add_cancel_r : forall n m p, (n | m) -> (n | m + p) -> (n | p).
Proof.
 intros n m p H H'. rewrite <- (add_simpl_l m p). now apply divide_sub_r.
Qed.

(** Properties of gcd *)

Lemma gcd_opp_l : forall n m, gcd (-n) m == gcd n m.
Proof.
 intros. apply gcd_unique_alt; try apply gcd_nonneg.
 intros. rewrite divide_opp_r. apply gcd_divide_iff.
Qed.

Lemma gcd_opp_r : forall n m, gcd n (-m) == gcd n m.
Proof.
 intros. now rewrite gcd_comm, gcd_opp_l, gcd_comm.
Qed.

Lemma gcd_abs_l : forall n m, gcd (abs n) m == gcd n m.
Proof.
 intros. destruct (abs_eq_or_opp n) as [H|H]; rewrite H.
 easy. apply gcd_opp_l.
Qed.

Lemma gcd_abs_r : forall n m, gcd n (abs m) == gcd n m.
Proof.
 intros. now rewrite gcd_comm, gcd_abs_l, gcd_comm.
Qed.

Lemma gcd_0_l : forall n, gcd 0 n == abs n.
Proof.
 intros. rewrite <- gcd_abs_r. apply gcd_0_l_nonneg, abs_nonneg.
Qed.

Lemma gcd_0_r : forall n, gcd n 0 == abs n.
Proof.
 intros. now rewrite gcd_comm, gcd_0_l.
Qed.

Lemma gcd_diag : forall n, gcd n n == abs n.
Proof.
 intros. rewrite <- gcd_abs_l, <- gcd_abs_r.
 apply gcd_diag_nonneg, abs_nonneg.
Qed.

Lemma gcd_add_mult_diag_r : forall n m p, gcd n (m+p*n) == gcd n m.
Proof.
 intros. apply gcd_unique_alt; try apply gcd_nonneg.
 intros. rewrite gcd_divide_iff. split; intros (U,V); split; trivial.
 apply divide_add_r; trivial. now apply divide_mul_r.
 apply divide_add_cancel_r with (p*n); trivial.
 now apply divide_mul_r. now rewrite add_comm.
Qed.

Lemma gcd_add_diag_r : forall n m, gcd n (m+n) == gcd n m.
Proof.
 intros n m. rewrite <- (mul_1_l n) at 2. apply gcd_add_mult_diag_r.
Qed.

Lemma gcd_sub_diag_r : forall n m, gcd n (m-n) == gcd n m.
Proof.
 intros n m. rewrite <- (mul_1_l n) at 2.
 rewrite <- add_opp_r, <- mul_opp_l. apply gcd_add_mult_diag_r.
Qed.

Definition Bezout n m p := exists a b, a*n + b*m == p.

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
 rewrite <- H. apply divide_add_r; now apply divide_mul_r.
Qed.

Lemma gcd_bezout : forall n m p, gcd n m == p -> Bezout n m p.
Proof.
 (* First, a version restricted to natural numbers *)
 assert (aux : forall n, 0<=n -> forall m, 0<=m -> Bezout n m (gcd n m)).
  intros n Hn; pattern n.
  apply strong_right_induction with (z:=0); trivial.
  unfold Bezout. solve_proper.
  clear n Hn. intros n Hn IHn.
  apply le_lteq in Hn; destruct Hn as [Hn|Hn].
  intros m Hm; pattern m.
  apply strong_right_induction with (z:=0); trivial.
  unfold Bezout. solve_proper.
  clear m Hm. intros m Hm IHm.
  destruct (lt_trichotomy n m) as [LT|[EQ|LT]].
  (* n < m *)
  destruct (IHm (m-n)) as (a & b & EQ).
  apply sub_nonneg; order.
  now apply lt_sub_pos.
  exists (a-b). exists b.
  rewrite gcd_sub_diag_r in EQ. rewrite <- EQ.
  rewrite mul_sub_distr_r, mul_sub_distr_l.
  now rewrite add_sub_assoc, add_sub_swap.
  (* n = m *)
  rewrite EQ. rewrite gcd_diag_nonneg; trivial.
  exists 1. exists 0. now nzsimpl.
  (* m < n *)
  destruct (IHn m Hm LT n) as (a & b & EQ). order.
  exists b. exists a. now rewrite gcd_comm, <- EQ, add_comm.
  (* n = 0 *)
  intros m Hm. rewrite <- Hn, gcd_0_l_nonneg; trivial.
  exists 0. exists 1. now nzsimpl.
 (* Then we relax the positivity condition on n *)
 assert (aux' : forall n m, 0<=m -> Bezout n m (gcd n m)).
  intros n m Hm.
  destruct (le_ge_cases 0 n). now apply aux.
  assert (Hn' : 0 <= -n) by now apply opp_nonneg_nonpos.
  destruct (aux (-n) Hn' m Hm) as (a & b & EQ).
  exists (-a). exists b. now rewrite <- gcd_opp_l, <- EQ, mul_opp_r, mul_opp_l.
 (* And finally we do the same for m *)
 intros n m p Hp. rewrite <- Hp; clear Hp.
 destruct (le_ge_cases 0 m). now apply aux'.
 assert (Hm' : 0 <= -m) by now apply opp_nonneg_nonpos.
 destruct (aux' n (-m) Hm') as (a & b & EQ).
 exists a. exists (-b). now rewrite <- gcd_opp_r, <- EQ, mul_opp_r, mul_opp_l.
Qed.

Lemma gcd_mul_mono_l :
  forall n m p, gcd (p * n) (p * m) == abs p * gcd n m.
Proof.
 intros n m p.
 apply gcd_unique.
 apply mul_nonneg_nonneg; trivial using gcd_nonneg, abs_nonneg.
 destruct (gcd_divide_l n m) as (q,Hq).
 rewrite Hq at 2. rewrite mul_assoc. apply mul_divide_mono_r.
 rewrite <- (abs_sgn p) at 2. rewrite <- mul_assoc. apply divide_factor_l.
 destruct (gcd_divide_r n m) as (q,Hq).
 rewrite Hq at 2. rewrite mul_assoc. apply mul_divide_mono_r.
 rewrite <- (abs_sgn p) at 2. rewrite <- mul_assoc. apply divide_factor_l.
 intros q H H'.
 destruct (gcd_bezout n m (gcd n m) (eq_refl _)) as (a & b & EQ).
 rewrite <- EQ, <- sgn_abs, mul_add_distr_l. apply divide_add_r.
 rewrite mul_shuffle2. now apply divide_mul_l.
 rewrite mul_shuffle2. now apply divide_mul_l.
Qed.

Lemma gcd_mul_mono_l_nonneg :
 forall n m p, 0<=p -> gcd (p*n) (p*m) == p * gcd n m.
Proof.
 intros. rewrite <- (abs_eq p) at 3; trivial. apply gcd_mul_mono_l.
Qed.

Lemma gcd_mul_mono_r :
 forall n m p, gcd (n * p) (m * p) == gcd n m * abs p.
Proof.
 intros n m p. now rewrite !(mul_comm _ p), gcd_mul_mono_l, mul_comm.
Qed.

Lemma gcd_mul_mono_r_nonneg :
 forall n m p, 0<=p -> gcd (n*p) (m*p) == gcd n m * p.
Proof.
 intros. rewrite <- (abs_eq p) at 3; trivial. apply gcd_mul_mono_r.
Qed.

Lemma gauss : forall n m p, (n | m * p) -> gcd n m == 1 -> (n | p).
Proof.
 intros n m p H G.
 destruct (gcd_bezout n m 1 G) as (a & b & EQ).
 rewrite <- (mul_1_l p), <- EQ, mul_add_distr_r.
 apply divide_add_r. rewrite mul_shuffle0. apply divide_factor_r.
 rewrite <- mul_assoc. now apply divide_mul_r.
Qed.

Lemma divide_mul_split : forall n m p, n ~= 0 -> (n | m * p) ->
 exists q r, n == q*r /\ (q | m) /\ (r | p).
Proof.
 intros n m p Hn H.
 assert (G := gcd_nonneg n m).
 apply le_lteq in G; destruct G as [G|G].
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
 rewrite <- gcd_mul_mono_r_nonneg, <- Hq, <- Hr; order.
 symmetry in G. apply gcd_eq_0 in G. destruct G as (Hn',_); order.
Qed.

(** TODO : more about rel_prime (i.e. gcd == 1), about prime ... *)

End ZGcdProp.
