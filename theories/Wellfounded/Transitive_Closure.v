(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Author: Bruno Barras *)

Require Import Relation_Definitions.
Require Import Relation_Operators.

Section Wf_Transitive_Closure.
  Variable A : Type.
  Variable R : relation A.

  Notation trans_clos := (clos_trans A R).

  Lemma incl_clos_trans : inclusion A R trans_clos.
    red; auto with sets.
  Qed.

  Lemma Acc_clos_trans : forall x:A, Acc R x -> Acc trans_clos x.
    induction 1 as [x0 _ H1].
    apply Acc_intro.
    intros y H2.
    induction H2; auto with sets.
    apply Acc_inv with y; auto with sets.
  Defined.

  #[local]
  Hint Resolve Acc_clos_trans : core.

  Lemma Acc_inv_trans : forall x y:A, trans_clos y x -> Acc R x -> Acc R y.
  Proof.
    induction 1 as [| x y]; auto with sets.
    intro; apply Acc_inv with y; assumption.
  Qed.

  Theorem wf_clos_trans : well_founded R -> well_founded trans_clos.
  Proof.
    unfold well_founded; auto with sets.
  Defined.

  Lemma wf_clos_trans_inverse_rel (B : Type) (Q : relation B) (F : B -> A -> Prop) :
    well_founded R ->
    (forall b, exists a, F b a) ->
    (forall b1 b2 a1, Q b2 b1 -> F b1 a1 -> exists a2, F b2 a2 /\ trans_clos a2 a1) ->
    well_founded Q.
  Proof.
    intros HR Hintro Hstep b.
    destruct (Hintro b) as [a H].
    revert b H.
    induction (wf_clos_trans HR a) as [a _ IH].
    intros b Hba.
    constructor.
    intros b' Hb'b.
    destruct (Hstep _ _ _ Hb'b Hba) as [? [??]].
    eapply IH; eassumption.
  Defined.

End Wf_Transitive_Closure.
