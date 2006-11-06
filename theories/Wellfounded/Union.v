(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Author: Bruno Barras *)

Require Import Relation_Operators.
Require Import Relation_Definitions.
Require Import Transitive_Closure.

Section WfUnion.
  Variable A : Set.
  Variables R1 R2 : relation A.
  
  Notation Union := (union A R1 R2).
  
  Remark strip_commut :
    commut R1 R2 ->
    forall x y:A, R1 x y ->
    forall z:A, clos_trans A R2 y z -> 
     exists2 y' : A, clos_trans A R2 x y' & R1 y' z.
  Proof.
    intros; generalize dependent x.
    induction H1 as [y z| y z x0 H0 IH1 H1 IH2]; intros.
    elim H with x y z; auto with sets; intros x0 H2 H3.
    exists x0; auto with sets.

    elim IH1 with x; auto with sets; intros.
    elim IH2 with x1; auto with sets; intros.
    exists x2; auto with sets.
    apply t_trans with x1; auto with sets.
  Qed.


  Lemma Acc_union :
    commut R1 R2 ->
    (forall x:A, Acc R1 x -> Acc R2 x) -> forall a:A, Acc R1 a -> Acc Union a.
  Proof.
    induction 3 as [x H1 H2].
    apply Acc_intro; intros.
    elim H3; intros; auto with sets.
    cut (clos_trans A R2 y x); auto with sets.
    elimtype (Acc (clos_trans A R2) y); intros.
    apply Acc_intro; intros.
    elim H8; intros.

    elim strip_commut with y0 x0 x; auto with sets; intros.
    apply Acc_inv_trans with x1; auto with sets.
    unfold union in |- *.
    elim H10; auto with sets; intros.
    apply t_trans with y1; auto with sets.

    apply H6; auto with sets.
    apply t_trans with x0; auto with sets.

    apply (Acc_clos_trans A).
    apply Acc_inv with x; auto with sets.
    apply H0.
    apply Acc_intro; auto with sets.
  Qed.

  Theorem wf_union :
    commut R1 R2 -> well_founded R1 -> well_founded R2 -> well_founded Union.
  Proof.
    unfold well_founded in |- *.
    intros.
    apply Acc_union; auto with sets.
  Qed.

End WfUnion.
