(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Bool ZArith.
Require Import ZifyClasses.
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

Instance Inj_comparison_Z : InjTyp comparison Z :=
  { inj := Z_of_comparison ; pred :=(fun x => -1 <= x <= 1) ; cstr := Z_of_comparison_bound}.
Add InjTyp Inj_comparison_Z.

Definition ZcompareZ (x y : Z) :=
  Z_of_comparison (Z.compare x y).

Program Instance BinOp_Zcompare : BinOp Z.compare :=
  { TBOp := ZcompareZ }.
Add BinOp BinOp_Zcompare.

Instance Op_eq_comparison : BinRel (@eq comparison) :=
  {TR := @eq Z ; TRInj := ltac:(destruct n,m; simpl ; intuition congruence) }.
Add BinRel Op_eq_comparison.

Instance Op_Eq : CstOp Eq :=
  { TCst := 0 ; TCstInj := eq_refl }.
Add CstOp Op_Eq.

Instance Op_Lt : CstOp Lt :=
  { TCst := -1 ; TCstInj := eq_refl }.
Add CstOp Op_Lt.

Instance Op_Gt : CstOp Gt :=
  { TCst := 1 ; TCstInj := eq_refl }.
Add CstOp Op_Gt.


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
    intuition.
  - rewrite Z.compare_lt_iff in C.
    intuition.
  - rewrite Z.compare_gt_iff in C.
    intuition.
Qed.

Instance ZcompareSpec : BinOpSpec ZcompareZ :=
  {| BPred := fun x y r => (x = y -> r = 0)
                           /\
                           (x > y -> r = 1)
                           /\
                           (x < y  -> r = -1)
              ; BSpec := Zcompare_spec|}.
Add Spec ZcompareSpec.
