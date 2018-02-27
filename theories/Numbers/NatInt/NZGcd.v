(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Greatest Common Divisor *)

Require Import NZAxioms NZMulOrder.

(** Interface of a gcd function, then its specification on naturals *)

Module Type Gcd (Import A : Typ).
 Parameter Inline gcd : t -> t -> t.
End Gcd.

Module Type NZGcdSpec (A : NZOrdAxiomsSig')(B : Gcd A).
 Import A B.
 Definition divide n m := exists p, m == p*n.
 Local Notation "( n | m )" := (divide n m) (at level 0).
 Axiom gcd_divide_l : forall n m, (gcd n m | n).
 Axiom gcd_divide_r : forall n m, (gcd n m | m).
 Axiom gcd_greatest : forall n m p, (p | n) -> (p | m) -> (p | gcd n m).
 Axiom gcd_nonneg : forall n m, 0 <= gcd n m.
End NZGcdSpec.

Module Type DivideNotation (A:NZOrdAxiomsSig')(B:Gcd A)(C:NZGcdSpec A B).
 Import A B C.
 Notation "( n | m )" := (divide n m) (at level 0).
End DivideNotation.

Module Type NZGcd (A : NZOrdAxiomsSig) := Gcd A <+ NZGcdSpec A.
Module Type NZGcd' (A : NZOrdAxiomsSig) :=
 Gcd A <+ NZGcdSpec A <+ DivideNotation A.

(** Derived properties of gcd *)

Module NZGcdProp
 (Import A : NZOrdAxiomsSig')
 (Import B : NZGcd' A)
 (Import C : NZMulOrderProp A).

(** Results concerning divisibility*)

Instance divide_wd : Proper (eq==>eq==>iff) divide.
Proof.
 unfold divide. intros x x' Hx y y' Hy.
 setoid_rewrite Hx. setoid_rewrite Hy. easy.
Qed.

Lemma divide_1_l : forall n, (1 | n).
Proof.
 intros n. exists n. now nzsimpl.
Qed.

Lemma divide_0_r : forall n, (n | 0).
Proof.
 intros n. exists 0. now nzsimpl.
Qed.

Lemma divide_0_l : forall n, (0 | n) -> n==0.
Proof.
 intros n (m,Hm). revert Hm. now nzsimpl.
Qed.

Lemma eq_mul_1_nonneg : forall n m,
 0<=n -> n*m == 1 -> n==1 /\ m==1.
Proof.
 intros n m Hn H.
 le_elim Hn.
 destruct (lt_ge_cases m 0) as [Hm|Hm].
 generalize (mul_pos_neg n m Hn Hm). order'.
 le_elim Hm.
 apply le_succ_l in Hn. rewrite <- one_succ in Hn.
 le_elim Hn.
 generalize (lt_1_mul_pos n m Hn Hm). order.
 rewrite <- Hn, mul_1_l in H. now split.
 rewrite <- Hm, mul_0_r in H. order'.
 rewrite <- Hn, mul_0_l in H. order'.
Qed.

Lemma eq_mul_1_nonneg' : forall n m,
 0<=m -> n*m == 1 -> n==1 /\ m==1.
Proof.
 intros n m Hm H. rewrite mul_comm in H.
 now apply and_comm, eq_mul_1_nonneg.
Qed.

Lemma divide_1_r_nonneg : forall n, 0<=n -> (n | 1) -> n==1.
Proof.
 intros n Hn (m,Hm). symmetry in Hm.
 now apply (eq_mul_1_nonneg' m n).
Qed.

Lemma divide_refl : forall n, (n | n).
Proof.
 intros n. exists 1. now nzsimpl.
Qed.

Lemma divide_trans : forall n m p, (n | m) -> (m | p) -> (n | p).
Proof.
 intros n m p (q,Hq) (r,Hr). exists (r*q).
 now rewrite Hr, Hq, mul_assoc.
Qed.

Instance divide_reflexive : Reflexive divide | 5 := divide_refl.
Instance divide_transitive : Transitive divide | 5 := divide_trans.

(** Due to sign, no general antisymmetry result *)

Lemma divide_antisym_nonneg : forall n m,
 0<=n -> 0<=m -> (n | m) -> (m | n) -> n == m.
Proof.
 intros n m Hn Hm (q,Hq) (r,Hr).
 le_elim Hn.
 destruct (lt_ge_cases q 0) as [Hq'|Hq'].
 generalize (mul_neg_pos q n Hq' Hn). order.
 rewrite Hq, mul_assoc in Hr. symmetry in Hr.
 apply mul_id_l in Hr; [|order].
 destruct (eq_mul_1_nonneg' r q) as [_ H]; trivial.
 now rewrite H, mul_1_l in Hq.
 rewrite <- Hn, mul_0_r in Hq. now rewrite <- Hn.
Qed.

Lemma mul_divide_mono_l : forall n m p, (n | m) -> (p * n | p * m).
Proof.
 intros n m p (q,Hq). exists q. now rewrite mul_shuffle3, Hq.
Qed.

Lemma mul_divide_mono_r : forall n m p, (n | m) -> (n * p | m * p).
Proof.
 intros n m p (q,Hq). exists q. now rewrite mul_assoc, Hq.
Qed.

Lemma mul_divide_cancel_l : forall n m p, p ~= 0 ->
 ((p * n | p * m) <-> (n | m)).
Proof.
 intros n m p Hp. split.
 intros (q,Hq). exists q. now rewrite mul_shuffle3, mul_cancel_l in Hq.
 apply mul_divide_mono_l.
Qed.

Lemma mul_divide_cancel_r : forall n m p, p ~= 0 ->
 ((n * p | m * p) <-> (n | m)).
Proof.
 intros. rewrite 2 (mul_comm _ p). now apply mul_divide_cancel_l.
Qed.

Lemma divide_add_r : forall n m p, (n | m) -> (n | p) -> (n | m + p).
Proof.
 intros n m p (q,Hq) (r,Hr). exists (q+r).
 now rewrite mul_add_distr_r, Hq, Hr.
Qed.

Lemma divide_mul_l : forall n m p, (n | m) -> (n | m * p).
Proof.
 intros n m p (q,Hq). exists (q*p). now rewrite mul_shuffle0, Hq.
Qed.

Lemma divide_mul_r : forall n m p, (n | p) -> (n | m * p).
Proof.
 intros n m p. rewrite mul_comm. apply divide_mul_l.
Qed.

Lemma divide_factor_l : forall n m, (n | n * m).
Proof.
 intros. apply divide_mul_l, divide_refl.
Qed.

Lemma divide_factor_r : forall n m, (n | m * n).
Proof.
 intros. apply divide_mul_r, divide_refl.
Qed.

Lemma divide_pos_le : forall n m, 0 < m -> (n | m) -> n <= m.
Proof.
 intros n m Hm (q,Hq).
 destruct (le_gt_cases n 0) as [Hn|Hn]. order.
 rewrite Hq.
 destruct (lt_ge_cases q 0) as [Hq'|Hq'].
 generalize (mul_neg_pos q n Hq' Hn). order.
 le_elim Hq'.
 rewrite <- (mul_1_l n) at 1. apply mul_le_mono_pos_r; trivial.
 now rewrite one_succ, le_succ_l.
 rewrite <- Hq', mul_0_l in Hq. order.
Qed.

(** Basic properties of gcd *)

Lemma gcd_unique : forall n m p,
 0<=p -> (p|n) -> (p|m) ->
 (forall q, (q|n) -> (q|m) -> (q|p)) ->
 gcd n m == p.
Proof.
 intros n m p Hp Hn Hm H.
 apply divide_antisym_nonneg; trivial. apply gcd_nonneg.
 apply H. apply gcd_divide_l. apply gcd_divide_r.
 now apply gcd_greatest.
Qed.

Instance gcd_wd : Proper (eq==>eq==>eq) gcd.
Proof.
 intros x x' Hx y y' Hy.
 apply gcd_unique.
 apply gcd_nonneg.
 rewrite Hx. apply gcd_divide_l.
 rewrite Hy. apply gcd_divide_r.
 intro. rewrite Hx, Hy. apply gcd_greatest.
Qed.

Lemma gcd_divide_iff : forall n m p,
  (p | gcd n m) <-> (p | n) /\ (p | m).
Proof.
 intros. split. split.
 transitivity (gcd n m); trivial using gcd_divide_l.
 transitivity (gcd n m); trivial using gcd_divide_r.
 intros (H,H'). now apply gcd_greatest.
Qed.

Lemma gcd_unique_alt : forall n m p, 0<=p ->
 (forall q, (q|p) <-> (q|n) /\ (q|m)) ->
 gcd n m == p.
Proof.
 intros n m p Hp H.
 apply gcd_unique; trivial.
 apply H. apply divide_refl.
 apply H. apply divide_refl.
 intros. apply H. now split.
Qed.

Lemma gcd_comm : forall n m, gcd n m == gcd m n.
Proof.
 intros. apply gcd_unique_alt; try apply gcd_nonneg.
 intros. rewrite and_comm. apply gcd_divide_iff.
Qed.

Lemma gcd_assoc : forall n m p, gcd n (gcd m p) == gcd (gcd n m) p.
Proof.
 intros. apply gcd_unique_alt; try apply gcd_nonneg.
 intros. now rewrite !gcd_divide_iff, and_assoc.
Qed.

Lemma gcd_0_l_nonneg : forall n, 0<=n -> gcd 0 n == n.
Proof.
 intros. apply gcd_unique; trivial.
 apply divide_0_r.
 apply divide_refl.
Qed.

Lemma gcd_0_r_nonneg : forall n, 0<=n -> gcd n 0 == n.
Proof.
 intros. now rewrite gcd_comm, gcd_0_l_nonneg.
Qed.

Lemma gcd_1_l : forall n, gcd 1 n == 1.
Proof.
 intros. apply gcd_unique; trivial using divide_1_l, le_0_1.
Qed.

Lemma gcd_1_r : forall n, gcd n 1 == 1.
Proof.
 intros. now rewrite gcd_comm, gcd_1_l.
Qed.

Lemma gcd_diag_nonneg : forall n, 0<=n -> gcd n n == n.
Proof.
 intros. apply gcd_unique; trivial using divide_refl.
Qed.

Lemma gcd_eq_0_l : forall n m, gcd n m == 0 -> n == 0.
Proof.
 intros.
 generalize (gcd_divide_l n m). rewrite H. apply divide_0_l.
Qed.

Lemma gcd_eq_0_r : forall n m, gcd n m == 0 -> m == 0.
Proof.
 intros. apply gcd_eq_0_l with n. now rewrite gcd_comm.
Qed.

Lemma gcd_eq_0 : forall n m, gcd n m == 0 <-> n == 0 /\ m == 0.
Proof.
 intros. split. split.
 now apply gcd_eq_0_l with m.
 now apply gcd_eq_0_r with n.
 intros (EQ,EQ'). rewrite EQ, EQ'. now apply gcd_0_r_nonneg.
Qed.

Lemma gcd_mul_diag_l : forall n m, 0<=n -> gcd n (n*m) == n.
Proof.
 intros n m Hn. apply gcd_unique_alt; trivial.
 intros q. split. split; trivial. now apply divide_mul_l.
 now destruct 1.
Qed.

Lemma divide_gcd_iff : forall n m, 0<=n -> ((n|m) <-> gcd n m == n).
Proof.
 intros n m Hn. split. intros (q,Hq). rewrite Hq.
 rewrite mul_comm. now apply gcd_mul_diag_l.
 intros EQ. rewrite <- EQ. apply gcd_divide_r.
Qed.

End NZGcdProp.
