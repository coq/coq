(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Import OrderedRing.
Require Import RingMicromega.
Require Import ZArith.
Require Import InitialRing.
Require Import Setoid.

Import OrderedRingSyntax.

Set Implicit Arguments.

Section InitialMorphism.

Variable R : Type.
Variables rO rI : R.
Variables rplus rtimes rminus: R -> R -> R.
Variable ropp : R -> R.
Variables req rle rlt : R -> R -> Prop.

Variable sor : SOR rO rI rplus rtimes rminus ropp req rle rlt.

Notation "0" := rO.
Notation "1" := rI.
Notation "x + y" := (rplus x y).
Notation "x * y " := (rtimes x y).
Notation "x - y " := (rminus x y).
Notation "- x" := (ropp x).
Notation "x == y" := (req x y).
Notation "x ~= y" := (~ req x y).
Notation "x <= y" := (rle x y).
Notation "x < y" := (rlt x y).

Lemma req_refl : forall x, req x x.
Proof.
  destruct sor.(SORsetoid) as (Equivalence_Reflexive,_,_).
  apply Equivalence_Reflexive.
Qed.

Lemma req_sym : forall x y, req x y -> req y x.
Proof.
  destruct sor.(SORsetoid) as (_,Equivalence_Symmetric,_).
  apply Equivalence_Symmetric.
Qed.

Lemma req_trans : forall x y z, req x y -> req y z -> req x z.
Proof.
  destruct sor.(SORsetoid) as (_,_,Equivalence_Transitive).
  apply Equivalence_Transitive.
Qed.


Add Relation R req
  reflexivity proved by sor.(SORsetoid).(@Equivalence_Reflexive _ _)
  symmetry proved by sor.(SORsetoid).(@Equivalence_Symmetric _ _)
  transitivity proved by sor.(SORsetoid).(@Equivalence_Transitive _ _)
as sor_setoid.

Add Morphism rplus with signature req ==> req ==> req as rplus_morph.
Proof.
exact sor.(SORplus_wd).
Qed.
Add Morphism rtimes with signature req ==> req ==> req as rtimes_morph.
Proof.
exact sor.(SORtimes_wd).
Qed.
Add Morphism ropp with signature req ==> req as ropp_morph.
Proof.
exact sor.(SORopp_wd).
Qed.
Add Morphism rle with signature req ==> req ==> iff as rle_morph.
Proof.
exact sor.(SORle_wd).
Qed.
Add Morphism rlt with signature req ==> req ==> iff as rlt_morph.
Proof.
exact sor.(SORlt_wd).
Qed.
Add Morphism rminus with signature req ==> req ==> req as rminus_morph.
Proof.
  exact (rminus_morph sor).
Qed.

Ltac le_less := rewrite (Rle_lt_eq sor); left; try assumption.
Ltac le_equal := rewrite (Rle_lt_eq sor); right; try reflexivity; try assumption.

Definition gen_order_phi_Z : Z -> R := gen_phiZ 0 1 rplus rtimes ropp.
Declare Equivalent Keys gen_order_phi_Z gen_phiZ.

Notation phi_pos := (gen_phiPOS 1 rplus rtimes).
Notation phi_pos1 := (gen_phiPOS1 1 rplus rtimes).

Notation "[ x ]" := (gen_order_phi_Z x).

Lemma ring_ops_wd : ring_eq_ext rplus rtimes ropp req.
Proof.
constructor.
exact rplus_morph.
exact rtimes_morph.
exact ropp_morph.
Qed.

Lemma Zring_morph :
  ring_morph 0 1 rplus rtimes rminus ropp req
             0%Z 1%Z Z.add Z.mul Z.sub Z.opp
             Zeq_bool gen_order_phi_Z.
Proof.
exact (gen_phiZ_morph sor.(SORsetoid) ring_ops_wd sor.(SORrt)).
Qed.

Lemma phi_pos1_pos : forall x : positive, 0 < phi_pos1 x.
Proof.
induction x as [x IH | x IH |]; simpl;
try apply (Rplus_pos_pos sor); try apply (Rtimes_pos_pos sor); try apply (Rplus_pos_pos sor);
try apply (Rlt_0_1 sor); assumption.
Qed.

Lemma phi_pos1_succ : forall x : positive, phi_pos1 (Pos.succ x) == 1 + phi_pos1 x.
Proof.
exact (ARgen_phiPOS_Psucc sor.(SORsetoid) ring_ops_wd
        (Rth_ARth sor.(SORsetoid) ring_ops_wd sor.(SORrt))).
Qed.

Lemma clt_pos_morph : forall x y : positive, (x < y)%positive -> phi_pos1 x < phi_pos1 y.
Proof.
intros x y H. pattern y; apply Pos.lt_ind with x.
rewrite phi_pos1_succ; apply (Rlt_succ_r sor).
clear y H; intros y _ H. rewrite phi_pos1_succ. now apply (Rlt_lt_succ sor).
assumption.
Qed.

Lemma clt_morph : forall x y : Z, (x < y)%Z -> [x] < [y].
Proof.
intros x y H.
do 2 rewrite (same_genZ sor.(SORsetoid) ring_ops_wd sor.(SORrt));
destruct x; destruct y; simpl in *; try discriminate.
apply phi_pos1_pos.
now apply clt_pos_morph.
apply <- (Ropp_neg_pos sor); apply phi_pos1_pos.
apply (Rlt_trans sor) with 0. apply <- (Ropp_neg_pos sor); apply phi_pos1_pos.
apply phi_pos1_pos.
apply -> (Ropp_lt_mono sor); apply clt_pos_morph.
red. now rewrite Pos.compare_antisym.
Qed.

Lemma Zcleb_morph : forall x y : Z, Z.leb x y = true -> [x] <= [y].
Proof.
unfold Z.leb; intros x y H.
case_eq (x ?= y)%Z; intro H1; rewrite H1 in H.
le_equal. apply Zring_morph.(morph_eq). unfold Zeq_bool; now rewrite H1.
le_less. now apply clt_morph.
discriminate.
Qed.

Lemma Zcneqb_morph : forall x y : Z, Zeq_bool x y = false -> [x] ~= [y].
Proof.
intros x y H. unfold Zeq_bool in H.
case_eq (Z.compare x y); intro H1; rewrite H1 in *; (discriminate || clear H).
apply (Rlt_neq sor). now apply clt_morph.
fold (x > y)%Z in H1. rewrite Z.gt_lt_iff in H1.
apply (Rneq_symm sor). apply (Rlt_neq sor). now apply clt_morph.
Qed.

End InitialMorphism.


