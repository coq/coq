(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Author: Bruno Barras *)

Require Import Relation_Operators.
Require Import Relation_Definitions.
Require Import Transitive_Closure.

Section WfUnion.
  Variable A : Type.
  Variables R1 R2 : relation A.

  Notation Union := (union A R1 R2).

  Remark strip_commut :
    commut A R1 R2 ->
    forall x y:A,
      clos_trans A R1 y x ->
      forall z:A, R2 z y ->  exists2 y' : A, R2 y' x & clos_trans A R1 z y'.
  Proof.
    induction 2 as [x y| x y z H0 IH1 H1 IH2]; intros.
    elim H with y x z; auto with sets; intros x0 H2 H3.
    exists x0; auto with sets.

    elim IH1 with z0; auto with sets; intros.
    elim IH2 with x0; auto with sets; intros.
    exists x1; auto with sets.
    apply t_trans with x0; auto with sets.
  Qed.


  Lemma Acc_union :
    commut A R1 R2 ->
    (forall x:A, Acc R2 x -> Acc R1 x) -> forall a:A, Acc R2 a -> Acc Union a.
  Proof.
    induction 3 as [x H1 H2].
    apply Acc_intro; intros.
    elim H3; intros; auto with sets.
    cut (clos_trans A R1 y x); auto with sets.
    elimtype (Acc (clos_trans A R1) y); intros.
    apply Acc_intro; intros.
    elim H8; intros.
    apply H6; auto with sets.
    apply t_trans with x0; auto with sets.

    elim strip_commut with x x0 y0; auto with sets; intros.
    apply Acc_inv_trans with x1; auto with sets.
    unfold union.
    elim H11; auto with sets; intros.
    apply t_trans with y1; auto with sets.

    apply (Acc_clos_trans A).
    apply Acc_inv with x; auto with sets.
    apply H0.
    apply Acc_intro; auto with sets.
  Qed.


  Theorem wf_union :
    commut A R1 R2 -> well_founded R1 -> well_founded R2 -> well_founded Union.
  Proof.
    unfold well_founded.
    intros.
    apply Acc_union; auto with sets.
  Qed.

End WfUnion.
