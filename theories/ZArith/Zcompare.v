(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $$ i*)

(**********************************************************************)
(** Binary Integers (Pierre Crégut, CNET, Lannion, France)            *)
(**********************************************************************)

Require Export BinPos BinInt.
Require Import Lt Gt Plus Mult.

Local Open Scope Z_scope.

(***************************)
(** * Comparison on integers *)

Lemma Zcompare_refl : forall n:Z, (n ?= n) = Eq.
Proof.
 destruct n as [|p|p]; simpl; trivial.
 apply Pcompare_refl.
 apply CompOpp_iff, Pcompare_refl.
Qed.

Lemma Zcompare_Eq_eq : forall n m:Z, (n ?= m) = Eq -> n = m.
Proof.
 intros [|x|x] [|y|y] H; simpl in *; try easy; f_equal.
  now apply Pcompare_Eq_eq.
  apply CompOpp_iff in H. now apply Pcompare_Eq_eq.
Qed.

Ltac destr_zcompare :=
 match goal with |- context [Zcompare ?x ?y] =>
  let H := fresh "H" in
  case_eq (Zcompare x y); intro H;
   [generalize (Zcompare_Eq_eq _ _ H); clear H; intro H |
    change (x<y)%Z in H |
    change (x>y)%Z in H ]
 end.

Lemma Zcompare_Eq_iff_eq : forall n m:Z, (n ?= m) = Eq <-> n = m.
Proof.
 intros x y; split; intro E; subst.
 now apply Zcompare_Eq_eq. now apply Zcompare_refl.
Qed.

Lemma Zcompare_antisym : forall n m:Z, CompOpp (n ?= m) = (m ?= n).
Proof.
 intros [|x|x] [|y|y]; simpl; try easy; f_equal; apply Pcompare_antisym.
Qed.

Lemma Zcompare_spec : forall n m, CompareSpec (n=m) (n<m) (m<n) (n ?= m).
Proof.
 intros.
 destruct (n?=m) as [ ]_eqn:H; constructor; trivial.
 now apply Zcompare_Eq_eq.
 red; now rewrite <- Zcompare_antisym, H.
Qed.

Lemma Zcompare_Gt_Lt_antisym : forall n m:Z, (n ?= m) = Gt <-> (m ?= n) = Lt.
Proof.
 intros x y.
 rewrite <- Zcompare_antisym. change Gt with (CompOpp Lt).
 split.
 auto using CompOpp_inj.
 intros; f_equal; auto.
Qed.

(** * Transitivity of comparison *)

Lemma Zcompare_Lt_trans :
  forall n m p:Z, (n ?= m) = Lt -> (m ?= p) = Lt -> (n ?= p) = Lt.
Proof.
 intros n m p; destruct n,m,p; simpl; try discriminate; trivial.
 eapply Plt_trans; eauto.
 rewrite 3 Pcompare_antisym; simpl. intros; eapply Plt_trans; eauto.
Qed.

Lemma Zcompare_Gt_trans :
  forall n m p:Z, (n ?= m) = Gt -> (m ?= p) = Gt -> (n ?= p) = Gt.
Proof.
  intros n m p Hnm Hmp.
  apply <- Zcompare_Gt_Lt_antisym.
  apply -> Zcompare_Gt_Lt_antisym in Hnm.
  apply -> Zcompare_Gt_Lt_antisym in Hmp.
  eapply Zcompare_Lt_trans; eauto.
Qed.

(** * Comparison and opposite *)

Lemma Zcompare_opp : forall n m:Z, (n ?= m) = (- m ?= - n).
Proof.
 destruct n, m; simpl; trivial; intros; now rewrite <- ZC4.
Qed.

(** * Comparison first-order specification *)

Lemma Zcompare_Gt_spec :
  forall n m:Z, (n ?= m) = Gt ->  exists h, n + - m = Zpos h.
Proof.
 intros [|p|p] [|q|q]; simpl; try discriminate.
 now exists q.
 now exists p.
 intros GT. exists (p-q)%positive. now rewrite GT.
 now exists (p+q)%positive.
 intros LT. apply CompOpp_iff in LT. simpl in LT.
 exists (q-p)%positive. now rewrite LT.
Qed.

(** * Comparison and addition *)

Local Hint Resolve Pcompare_refl.

Lemma weak_Zcompare_plus_compat :
  forall (n m:Z) (p:positive), (Zpos p + n ?= Zpos p + m) = (n ?= m).
Proof.
 intros [|x|x] [|y|y] z; simpl; trivial; try apply ZC2;
  try apply Plt_plus_r.
 case Pcompare_spec; intros E0; trivial; try apply ZC2;
  now apply Pminus_decr.
 apply Pplus_compare_mono_l.
 case Pcompare_spec; intros E0; trivial; try apply ZC2.
  apply Plt_trans with z. now apply Pminus_decr. apply Plt_plus_r.
 case Pcompare_spec; intros E0; trivial; try apply ZC2.
  now apply Pminus_decr.
 case Pcompare_spec; intros E0; trivial; try apply ZC2.
  apply Plt_trans with z. now apply Pminus_decr. apply Plt_plus_r.
 case Pcompare_spec; intros E0; simpl; subst.
  now case Pcompare_spec.
  case Pcompare_spec; intros E1; simpl; subst; trivial.
  now rewrite <- ZC4.
  f_equal.
  apply Pminus_compare_mono_r; trivial.
  rewrite <- ZC4. symmetry. now apply Plt_trans with z.
  case Pcompare_spec; intros E1; simpl; subst; trivial.
  now rewrite E0.
  symmetry. apply CompOpp_iff. now apply Plt_trans with z.
  rewrite <- ZC4.
  apply Pminus_compare_mono_l; trivial.
Qed.

Lemma Zcompare_plus_compat : forall n m p:Z, (p + n ?= p + m) = (n ?= m).
Proof.
 intros x y [|z|z]; trivial.
 apply weak_Zcompare_plus_compat.
 rewrite (Zcompare_opp x y), Zcompare_opp, 2 Zopp_plus_distr, Zopp_neg.
 apply weak_Zcompare_plus_compat.
Qed.

Lemma Zplus_compare_compat :
  forall (r:comparison) (n m p q:Z),
    (n ?= m) = r -> (p ?= q) = r -> (n + p ?= m + q) = r.
Proof.
 intros [ | | ] x y z t H H'.
 apply Zcompare_Eq_eq in H. apply Zcompare_Eq_eq in H'. subst.
  apply Zcompare_refl.
 apply Zcompare_Lt_trans with (y+z).
 now rewrite 2 (Zplus_comm _ z), Zcompare_plus_compat.
 now rewrite Zcompare_plus_compat.
 apply Zcompare_Gt_trans with (y+z).
 now rewrite 2 (Zplus_comm _ z), Zcompare_plus_compat.
 now rewrite Zcompare_plus_compat.
Qed.

Lemma Zcompare_succ_Gt : forall n:Z, (Zsucc n ?= n) = Gt.
Proof.
 intro x; unfold Zsucc; pattern x at 2; rewrite <- (Zplus_0_r x);
  now rewrite Zcompare_plus_compat.
Qed.

Lemma Zcompare_Gt_not_Lt : forall n m:Z, (n ?= m) = Gt <-> (n ?= m+1) <> Lt.
Proof.
 intros x y; split; intros H.
 (* -> *)
 destruct (Zcompare_Gt_spec _ _ H) as (h,EQ).
 replace x with (y+Zpos h) by (rewrite <- EQ; apply Zplus_minus).
 rewrite Zcompare_plus_compat. apply Plt_1.
 (* <- *)
 assert (H' := Zcompare_succ_Gt y).
 destruct (Zcompare_spec x (y+1)) as [->|LT|GT]; trivial.
  now elim H.
  apply Zcompare_Gt_Lt_antisym in GT.
   apply Zcompare_Gt_trans with (y+1); trivial.
Qed.

(** * Successor and comparison *)

Lemma Zcompare_succ_compat : forall n m:Z, (Zsucc n ?= Zsucc m) = (n ?= m).
Proof.
 intros n m; unfold Zsucc;
  now rewrite 2 (Zplus_comm _ 1), Zcompare_plus_compat.
Qed.

(** * Multiplication and comparison *)

Lemma Zcompare_mult_compat :
  forall (p:positive) (n m:Z), (Zpos p * n ?= Zpos p * m) = (n ?= m).
Proof.
 intros p [|n|n] [|m|m]; simpl; trivial.
  apply Pmult_compare_mono_l.
  f_equal. apply Pmult_compare_mono_l.
Qed.

(** * Reverting [x ?= y] to trichotomy *)

Lemma Zcompare_elim :
  forall (c1 c2 c3:Prop) (n m:Z),
    (n = m -> c1) ->
    (n < m -> c2) ->
    (n > m -> c3) -> match n ?= m with
                       | Eq => c1
                       | Lt => c2
                       | Gt => c3
                     end.
Proof.
 intros c1 c2 c3 x y EQ LT GT; intros.
 case Zcompare_spec; auto.
 intro H. apply GT. red. now rewrite <- Zcompare_antisym, H.
Qed.

Lemma Zcompare_eq_case :
  forall (c1 c2 c3:Prop) (n m:Z),
    c1 -> n = m -> match n ?= m with
                     | Eq => c1
                     | Lt => c2
                     | Gt => c3
                   end.
Proof.
  intros c1 c2 c3 x y; intros.
  rewrite H0; rewrite Zcompare_refl.
  assumption.
Qed.

(** * Decompose an egality between two [?=] relations into 3 implications *)

Lemma Zcompare_egal_dec :
  forall n m p q:Z,
    (n < m -> p < q) ->
    ((n ?= m) = Eq -> (p ?= q) = Eq) ->
    (n > m -> p > q) -> (n ?= m) = (p ?= q).
Proof.
  intros x1 y1 x2 y2.
  unfold Zgt; unfold Zlt; case (x1 ?= y1); case (x2 ?= y2);
    auto with arith; symmetry; auto with arith.
Qed.

(** * Relating [x ?= y] to [Zle], [Zlt], [Zge] or [Zgt] *)

Lemma Zle_compare :
  forall n m:Z,
    n <= m -> match n ?= m with
		| Eq => True
		| Lt => True
		| Gt => False
              end.
Proof.
  intros x y; unfold Zle; elim (x ?= y); auto with arith.
Qed.

Lemma Zlt_compare :
  forall n m:Z,
   n < m -> match n ?= m with
              | Eq => False
              | Lt => True
              | Gt => False
            end.
Proof.
  intros x y; unfold Zlt in |- *; elim (x ?= y); intros;
    discriminate || trivial with arith.
Qed.

Lemma Zge_compare :
  forall n m:Z,
    n >= m -> match n ?= m with
		| Eq => True
		| Lt => False
		| Gt => True
              end.
Proof.
  intros x y; unfold Zge; elim (x ?= y); auto.
Qed.

Lemma Zgt_compare :
  forall n m:Z,
    n > m -> match n ?= m with
               | Eq => False
               | Lt => False
               | Gt => True
             end.
Proof.
  intros x y; unfold Zgt; now elim (x ?= y).
Qed.

(*********************)
(** * Other properties *)

Lemma Zmult_compare_compat_l :
  forall n m p:Z, p > 0 -> (n ?= m) = (p * n ?= p * m).
Proof.
  intros x y z H; destruct z.
  discriminate H.
  rewrite Zcompare_mult_compat; reflexivity.
  discriminate H.
Qed.

Lemma Zmult_compare_compat_r :
  forall n m p:Z, p > 0 -> (n ?= m) = (n * p ?= m * p).
Proof.
  intros x y z H; rewrite 2 (Zmult_comm _ z);
    apply Zmult_compare_compat_l; assumption.
Qed.

(*************************)
(** * Basic properties of minimum and maximum *)

Lemma Zmax_l : forall x y, y<=x -> Zmax x y = x.
Proof.
 unfold Zle, Zmax. intros x y. rewrite <- (Zcompare_antisym x y).
 destruct (x ?= y); intuition.
Qed.

Lemma Zmax_r : forall x y, x<=y -> Zmax x y = y.
Proof.
 unfold Zle, Zmax. intros x y. generalize (Zcompare_Eq_eq x y).
 destruct (x ?= y); intuition.
Qed.

Lemma Zmin_l : forall x y, x<=y -> Zmin x y = x.
Proof.
 unfold Zle, Zmin. intros x y. generalize (Zcompare_Eq_eq x y).
 destruct (x ?= y); intuition.
Qed.

Lemma Zmin_r : forall x y, y<=x -> Zmin x y = y.
Proof.
 unfold Zle, Zmin. intros x y.
 rewrite <- (Zcompare_antisym x y). generalize (Zcompare_Eq_eq x y).
 destruct (x ?= y); intuition.
Qed.


(**************************)
(** * Basic properties of [Zabs] *)

Lemma Zabs_eq : forall n:Z, 0 <= n -> Zabs n = n.
Proof.
 destruct n; auto. now destruct 1.
Qed.

Lemma Zabs_non_eq : forall n:Z, n <= 0 -> Zabs n = - n.
Proof.
 destruct n; auto. now destruct 1.
Qed.

(**************************)
(** * Basic properties of [Zsign] *)

Lemma Zsgn_0 : forall x, x = 0 -> Zsgn x = 0.
Proof.
 intros. now subst.
Qed.

Lemma Zsgn_1 : forall x, 0 < x -> Zsgn x = 1.
Proof.
 destruct x; auto; discriminate.
Qed.

Lemma Zsgn_m1 : forall x, x < 0 -> Zsgn x = -1.
Proof.
 destruct x; auto; discriminate.
Qed.
