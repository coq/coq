(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(****************************************************************************)
(*                              Bruno Barras                                *)
(****************************************************************************)

Require Relation_Definitions.

Section WfInclusion.
  Variable A:Set.
  Variable R1,R2:A->A->Prop.

  Lemma Acc_incl: (inclusion A R1 R2)->(z:A)(Acc A R2 z)->(Acc A R1 z).
  Proof.
    Induction 2;Intros.
    Apply Acc_intro;Auto with sets.
  Save.

  Hints Resolve Acc_incl.

  Theorem wf_incl: 
         (inclusion A R1 R2)->(well_founded A R2)->(well_founded A R1).
  Proof.
    Unfold well_founded ;Auto with sets.
  Save.

End WfInclusion.
