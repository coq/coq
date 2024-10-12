(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Bool ZArith.
Require Import Zify ZifyClasses.
Require Import Lia.
Local Open Scope Z_scope.

(** [Z_of_comparison] is the injection function for comparison *)
Definition Z_of_comparison (c : comparison) : Z :=
  match c with
  | Lt => -1
  | Eq => 0
  | Gt => 1
  end.

Lemma Z_of_comparison_bound : forall x,   -1 <= Z_of_comparison x <= 1.
Proof.
  destruct x ; simpl; compute; intuition congruence.
Qed.

#[global]
Instance Inj_comparison_Z : InjTyp comparison Z :=
  { inj := Z_of_comparison ; pred :=(fun x => -1 <= x <= 1) ; cstr := Z_of_comparison_bound}.
Add Zify InjTyp Inj_comparison_Z.

Definition ZcompareZ (x y : Z) :=
  Z_of_comparison (Z.compare x y).

#[global]
Program Instance BinOp_Zcompare : BinOp Z.compare :=
  { TBOp := ZcompareZ }.
Add Zify BinOp BinOp_Zcompare.

#[global]
Instance Op_eq_comparison : BinRel (@eq comparison) :=
  {TR := @eq Z ; TRInj := ltac:(intros [] []; simpl ; intuition congruence) }.
Add Zify BinRel Op_eq_comparison.

#[global]
Instance Op_Eq : CstOp Eq :=
  { TCst := 0 ; TCstInj := eq_refl }.
Add Zify CstOp Op_Eq.

#[global]
Instance Op_Lt : CstOp Lt :=
  { TCst := -1 ; TCstInj := eq_refl }.
Add Zify CstOp Op_Lt.

#[global]
Instance Op_Gt : CstOp Gt :=
  { TCst := 1 ; TCstInj := eq_refl }.
Add Zify CstOp Op_Gt.


Lemma Zcompare_spec : forall x y,
    (x = y -> ZcompareZ x y = 0)
    /\
    (x > y -> ZcompareZ x y = 1)
    /\
    (x < y  -> ZcompareZ x y = -1).
Proof.
  unfold ZcompareZ.
  intros.
  destruct (x ?= y) eqn:C; simpl.
  - rewrite Z.compare_eq_iff in C.
    lia.
  - rewrite Z.compare_lt_iff in C.
    lia.
  - rewrite Z.compare_gt_iff in C.
    lia.
Qed.

#[global]
Instance ZcompareSpec : BinOpSpec ZcompareZ :=
  {| BPred := fun x y r => (x = y -> r = 0)
                           /\
                           (x > y -> r = 1)
                           /\
                           (x < y  -> r = -1)
              ; BSpec := Zcompare_spec|}.
Add Zify BinOpSpec ZcompareSpec.
