(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Author: Bruno Barras *)

Require Relation_Definitions.
Require Relation_Operators.

Section Wf_Transitive_Closure.
  Variable A: Set.
  Variable R: (relation A).

  Notation trans_clos := (clos_trans A R).
 
  Lemma incl_clos_trans: (inclusion A R trans_clos).
    Red;Auto with sets.
  Qed.

  Lemma Acc_clos_trans: (x:A)(Acc A R x)->(Acc A trans_clos x).
    NewInduction 1 as [x0 _ H1].
    Apply Acc_intro.
    Intros y H2.
    NewInduction H2;Auto with sets.
    Apply Acc_inv with y ;Auto with sets.
  Qed.

  Hints Resolve Acc_clos_trans.

  Lemma Acc_inv_trans: (x,y:A)(trans_clos y x)->(Acc A R x)->(Acc A R y).
  Proof.
    NewInduction 1 as [|x y];Auto with sets.
    Intro; Apply Acc_inv with y; Assumption.
  Qed.

  Theorem wf_clos_trans: (well_founded A R)  ->(well_founded A trans_clos).
  Proof.
    Unfold well_founded;Auto with sets.
  Qed.

End Wf_Transitive_Closure.
