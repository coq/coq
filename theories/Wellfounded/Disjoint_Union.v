(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Author: Cristina Cornes
    From : Constructing Recursion Operators in Type Theory
           L. Paulson  JSC (1986) 2, 325-355 *)

Require Import Relation_Operators.

Section Wf_Disjoint_Union.
  Variables A B : Type.
  Variable leA : A -> A -> Prop.
  Variable leB : B -> B -> Prop.

  Notation Le_AsB := (le_AsB A B leA leB).

  Lemma acc_A_sum : forall x:A, Acc leA x -> Acc Le_AsB (inl B x).
  Proof.
    induction 1.
    apply Acc_intro; intros y H2.
    inversion_clear H2.
    auto with sets.
  Qed.

  Lemma acc_B_sum :
    well_founded leA -> forall x:B, Acc leB x -> Acc Le_AsB (inr A x).
  Proof.
    induction 2.
    apply Acc_intro; intros y H3.
    inversion_clear H3; auto with sets.
    apply acc_A_sum; auto with sets.
  Qed.


  Lemma wf_disjoint_sum :
    well_founded leA -> well_founded leB -> well_founded Le_AsB.
  Proof.
    intros.
    unfold well_founded.
    destruct a as [a| b].
    apply (acc_A_sum a).
    apply (H a).

    apply (acc_B_sum H b).
    apply (H0 b).
  Qed.

End Wf_Disjoint_Union.
