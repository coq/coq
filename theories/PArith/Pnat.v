(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import BinPos Le Lt Gt Plus Mult Minus Compare_dec Wf_nat.

(** Properties of the injection from binary positive numbers
    to Peano natural numbers *)

(** Original development by Pierre Crégut, CNET, Lannion, France *)

Local Open Scope positive_scope.
Local Open Scope nat_scope.

(** [Pmult_nat] in term of [nat_of_P] *)

Lemma Pmult_nat_mult : forall p n,
 Pmult_nat p n = nat_of_P p * n.
Proof.
 induction p; intros n.
 unfold nat_of_P. simpl. f_equal. rewrite 2 IHp.
 rewrite <- mult_assoc. f_equal. simpl. now rewrite <- plus_n_O.
 unfold nat_of_P. simpl. rewrite 2 IHp.
 rewrite <- mult_assoc. f_equal. simpl. now rewrite <- plus_n_O.
 simpl. now rewrite <- plus_n_O.
Qed.

(** [nat_of_P] is a morphism for successor, addition, multiplication *)

Lemma Psucc_S : forall p, nat_of_P (Psucc p) = S (nat_of_P p).
Proof.
 induction p; unfold nat_of_P; simpl; trivial.
  now rewrite !Pmult_nat_mult, IHp.
Qed.

Theorem Pplus_plus :
 forall p q, nat_of_P (p + q) = nat_of_P p + nat_of_P q.
Proof.
 induction p using Pind; intros q.
 now rewrite <- Pplus_one_succ_l, Psucc_S.
 now rewrite Pplus_succ_permute_l, !Psucc_S, IHp.
Qed.

Theorem Pmult_mult :
 forall p q, nat_of_P (p * q) = nat_of_P p * nat_of_P q.
Proof.
 induction p using Pind; simpl; intros; trivial.
 now rewrite Pmult_Sn_m, Pplus_plus, IHp, Psucc_S.
Qed.

(** Mapping of xH, xO and xI through [nat_of_P] *)

Lemma nat_of_P_xH : nat_of_P 1 = 1.
Proof.
 reflexivity.
Qed.

Lemma nat_of_P_xO : forall p, nat_of_P (xO p) = 2 * nat_of_P p.
Proof.
 intros. exact (Pmult_mult 2 p).
Qed.

Lemma nat_of_P_xI : forall p, nat_of_P (xI p) = S (2 * nat_of_P p).
Proof.
 intros. now rewrite xI_succ_xO, Psucc_S, nat_of_P_xO.
Qed.

(** [nat_of_P] maps to the strictly positive subset of [nat] *)

Lemma nat_of_P_is_S : forall p, exists n, nat_of_P p = S n.
Proof.
induction p as [p (h,IH)| p (h,IH)| ]; unfold nat_of_P; simpl.
 exists (S h * 2). now rewrite Pmult_nat_mult, IH.
 exists (S (h*2)). now rewrite Pmult_nat_mult,IH.
 now exists 0.
Qed.

(** [nat_of_P] is strictly positive *)

Lemma nat_of_P_pos : forall p, 0 < nat_of_P p.
Proof.
 intros p. destruct (nat_of_P_is_S p) as (n,->). auto with arith.
Qed.

(** [nat_of_P] is a morphism for comparison *)

Lemma Pcompare_nat_compare : forall p q,
 (p ?= q) = nat_compare (nat_of_P p) (nat_of_P q).
Proof.
 induction p as [ |p IH] using Pind; intros q.
 destruct (Psucc_pred q) as [Hq|Hq]; [now subst|].
 rewrite <- Hq, Plt_1_succ, Psucc_S, nat_of_P_xH, nat_compare_S.
 symmetry. apply nat_compare_lt, nat_of_P_pos.
 destruct (Psucc_pred q) as [Hq|Hq]; [subst|].
 rewrite Pos.compare_antisym, Plt_1_succ, Psucc_S. simpl.
 symmetry. apply nat_compare_gt, nat_of_P_pos.
 now rewrite <- Hq, 2 Psucc_S, Pcompare_succ_succ, IH.
Qed.

(** [nat_of_P] is hence injective *)

Lemma nat_of_P_inj_iff : forall p q, nat_of_P p = nat_of_P q <-> p = q.
Proof.
 intros.
 eapply iff_trans; [eapply iff_sym|eapply Pcompare_eq_iff].
 rewrite Pcompare_nat_compare.
 apply nat_compare_eq_iff.
Qed.

Lemma nat_of_P_inj : forall p q, nat_of_P p = nat_of_P q -> p = q.
Proof.
 intros. now apply nat_of_P_inj_iff.
Qed.

(** [nat_of_P] is a morphism for [lt], [le], etc *)

Lemma Plt_lt : forall p q, Plt p q <-> nat_of_P p < nat_of_P q.
Proof.
 intros. unfold Plt. rewrite Pcompare_nat_compare.
 apply iff_sym, nat_compare_lt.
Qed.

Lemma Ple_le : forall p q, Ple p q <-> nat_of_P p <= nat_of_P q.
Proof.
 intros. unfold Ple. rewrite Pcompare_nat_compare.
 apply iff_sym, nat_compare_le.
Qed.

Lemma Pgt_gt : forall p q, Pgt p q <-> nat_of_P p > nat_of_P q.
Proof.
 intros. unfold Pgt. rewrite Pcompare_nat_compare.
 apply iff_sym, nat_compare_gt.
Qed.

Lemma Pge_ge : forall p q, Pge p q <-> nat_of_P p >= nat_of_P q.
Proof.
 intros. unfold Pge. rewrite Pcompare_nat_compare.
 apply iff_sym, nat_compare_ge.
Qed.

(** [nat_of_P] is a morphism for subtraction *)

Theorem Pminus_minus :
 forall p q, Plt q p -> nat_of_P (p - q) = nat_of_P p - nat_of_P q.
Proof.
 intros x y H; apply plus_reg_l with (nat_of_P y); rewrite le_plus_minus_r.
 rewrite <- Pplus_plus, Pplus_minus. trivial. now apply ZC2.
 now apply lt_le_weak, Plt_lt.
Qed.

(** Results about [Pmult_nat], many are old intermediate results *)

Lemma Pmult_nat_succ_morphism :
 forall p n, Pmult_nat (Psucc p) n = n + Pmult_nat p n.
Proof.
 intros. now rewrite !Pmult_nat_mult, Psucc_S.
Qed.

Theorem Pmult_nat_l_plus_morphism :
 forall p q n, Pmult_nat (p + q) n = Pmult_nat p n + Pmult_nat q n.
Proof.
 intros. rewrite !Pmult_nat_mult, Pplus_plus. apply mult_plus_distr_r.
Qed.

Theorem Pmult_nat_plus_carry_morphism :
 forall p q n, Pmult_nat (Pplus_carry p q) n = n + Pmult_nat (p + q) n.
Proof.
 intros. now rewrite Pplus_carry_spec, Pmult_nat_succ_morphism.
Qed.

Lemma Pmult_nat_r_plus_morphism :
 forall p n, Pmult_nat p (n + n) = Pmult_nat p n + Pmult_nat p n.
Proof.
 intros. rewrite !Pmult_nat_mult. apply mult_plus_distr_l.
Qed.

Lemma ZL6 : forall p, Pmult_nat p 2 = nat_of_P p + nat_of_P p.
Proof.
 intros. rewrite Pmult_nat_mult, mult_comm. simpl. now rewrite <- plus_n_O.
Qed.

Lemma le_Pmult_nat : forall p n, n <= Pmult_nat p n.
Proof.
 intros. rewrite Pmult_nat_mult.
 apply le_trans with (1*n). now rewrite mult_1_l.
 apply mult_le_compat_r. apply nat_of_P_pos.
Qed.

(** [nat_of_P] is a morphism for [iter_pos] and [iter_nat] *)

Theorem iter_nat_of_P :
  forall p (A:Type) (f:A->A) (x:A),
    iter_pos p A f x = iter_nat (nat_of_P p) A f x.
Proof.
 induction p as [p IH|p IH| ]; intros A f x; simpl; trivial.
 f_equal. now rewrite 2 IH, <- iter_nat_plus, <- ZL6.
 now rewrite 2 IH, <- iter_nat_plus, <- ZL6.
Qed.

(**********************************************************************)
(** Properties of the shifted injection from Peano natural numbers to
    binary positive numbers *)

(** Composition of [P_of_succ_nat] and [nat_of_P] is successor on [nat] *)

Theorem nat_of_P_of_succ_nat :
 forall n, nat_of_P (P_of_succ_nat n) = S n.
Proof.
induction n as [|n H]; trivial; simpl; now rewrite Psucc_S, H.
Qed.

(** Composition of [nat_of_P] and [P_of_succ_nat] is successor on [positive] *)

Theorem P_of_succ_nat_of_P :
 forall p, P_of_succ_nat (nat_of_P p) = Psucc p.
Proof.
intros.
apply nat_of_P_inj. now rewrite nat_of_P_of_succ_nat, Psucc_S.
Qed.

(** Composition of [nat_of_P], [P_of_succ_nat] and [Ppred] is identity
    on [positive] *)

Theorem Ppred_of_succ_nat_of_P :
 forall p, Ppred (P_of_succ_nat (nat_of_P p)) = p.
Proof.
intros; rewrite P_of_succ_nat_of_P, Ppred_succ; auto.
Qed.

(**********************************************************************)
(** Extra properties of the injection from binary positive numbers
    to Peano natural numbers *)

(** Old names and old-style lemmas *)

Notation nat_of_P_succ_morphism := Psucc_S (only parsing).
Notation nat_of_P_plus_morphism := Pplus_plus (only parsing).
Notation nat_of_P_mult_morphism := Pmult_mult (only parsing).
Notation nat_of_P_compare_morphism := Pcompare_nat_compare (only parsing).
Notation lt_O_nat_of_P := nat_of_P_pos (only parsing).
Notation ZL4 := nat_of_P_is_S (only parsing).
Notation nat_of_P_o_P_of_succ_nat_eq_succ := nat_of_P_of_succ_nat (only parsing).
Notation P_of_succ_nat_o_nat_of_P_eq_succ := P_of_succ_nat_of_P (only parsing).
Notation pred_o_P_of_succ_nat_o_nat_of_P_eq_id := Ppred_of_succ_nat_of_P
 (only parsing).

Definition nat_of_P_minus_morphism p q :
 (p ?= q) = Gt -> nat_of_P (p - q) = nat_of_P p - nat_of_P q
 := fun H => Pminus_minus p q (ZC1 _ _ H).

Definition nat_of_P_lt_Lt_compare_morphism p q :
 (p ?= q) = Lt -> nat_of_P p < nat_of_P q
 := proj1 (Plt_lt p q).

Definition nat_of_P_gt_Gt_compare_morphism p q :
 (p ?= q) = Gt -> nat_of_P p > nat_of_P q
 := proj1 (Pgt_gt p q).

Definition nat_of_P_lt_Lt_compare_complement_morphism p q :
 nat_of_P p < nat_of_P q -> (p ?= q) = Lt
 := proj2 (Plt_lt p q).

Definition nat_of_P_gt_Gt_compare_complement_morphism p q :
 nat_of_P p > nat_of_P q -> (p ?= q) = Gt
 := proj2 (Pgt_gt p q).
