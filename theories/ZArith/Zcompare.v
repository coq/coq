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
 exact Z.lt_trans.
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

Lemma Zcompare_opp : forall n m, (n ?= m) = (- m ?= - n).
Proof.
 symmetry. apply Z.compare_opp.
Qed.

(** * Comparison first-order specification *)

Lemma Zcompare_Gt_spec :
  forall n m, (n ?= m) = Gt ->  exists h, n + - m = Zpos h.
Proof.
 intros n m H. rewrite Z.compare_sub in H. unfold Z.sub in H.
 destruct (n+-m) as [|p|p]; try discriminate. now exists p.
Qed.

(** * Comparison and addition *)

Lemma Zcompare_plus_compat : forall n m p, (p + n ?= p + m) = (n ?= m).
Proof.
 intros. apply Z.add_compare_mono_l.
Qed.

Lemma Zplus_compare_compat :
  forall (r:comparison) (n m p q:Z),
    (n ?= m) = r -> (p ?= q) = r -> (n + p ?= m + q) = r.
Proof.
 intros r n m p q.
 rewrite (Z.compare_sub n), (Z.compare_sub p), (Z.compare_sub (n+p)).
 unfold Z.sub. rewrite Z.BootStrap.opp_add_distr.
 rewrite <- Z.BootStrap.add_assoc, (Z.BootStrap.add_assoc p).
 rewrite (Z.BootStrap.add_comm p (-m)).
 rewrite <- Z.BootStrap.add_assoc,  (Z.BootStrap.add_assoc n).
 destruct (n+-m), (p+-q); simpl; intros; now subst.
Qed.

Lemma Zcompare_succ_Gt : forall n:Z, (Zsucc n ?= n) = Gt.
Proof.
 intro x; unfold Zsucc; pattern x at 2; rewrite <- (Zplus_0_r x);
  now rewrite Zcompare_plus_compat.
Qed.

Lemma Zcompare_Gt_not_Lt : forall n m:Z, (n ?= m) = Gt <-> (n ?= m+1) <> Lt.
Proof.
 intros n m. rewrite 2 (Z.compare_sub n).
 unfold Z.sub. rewrite Z.BootStrap.opp_add_distr.
 rewrite Z.BootStrap.add_assoc.
 destruct (n+-m) as [|[ | | ]|]; simpl; easy'.
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

Notation Zmin_l := Z.min_l (only parsing).
Notation Zmin_r := Z.min_r (only parsing).
Notation Zmax_l := Z.max_l (only parsing).
Notation Zmax_r := Z.max_r (only parsing).
Notation Zabs_eq := Z.abs_eq (only parsing).
Notation Zabs_non_eq := Z.abs_neq (only parsing).
Notation Zsgn_0 := Z.sgn_null (only parsing).
Notation Zsgn_1 := Z.sgn_pos (only parsing).
Notation Zsgn_m1 := Z.sgn_neg (only parsing).

