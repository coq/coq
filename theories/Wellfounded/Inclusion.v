(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Author: Bruno Barras *)

Require Import Relation_Definitions.

Section WfInclusion.
  Variable A : Set.
  Variables R1 R2 : A -> A -> Prop.

  Lemma Acc_incl : inclusion A R1 R2 -> forall z:A, Acc R2 z -> Acc R1 z.
  Proof.
    induction 2.
    apply Acc_intro; auto with sets.
  Qed.
  
  Hint Resolve Acc_incl.

  Theorem wf_incl : inclusion A R1 R2 -> well_founded R2 -> well_founded R1.
  Proof.
    unfold well_founded in |- *; auto with sets.
  Qed.

End WfInclusion.