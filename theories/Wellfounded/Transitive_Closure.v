
(* $Id$ *)

(****************************************************************************)
(*                              Bruno Barras                                *)
(****************************************************************************)

Require Relation_Definitions.
Require Relation_Operators.

Section Wf_Transitive_Closure.
  Variable A: Set.
  Variable R: (relation A).

  Syntactic Definition trans_clos := (clos_trans A R).
 
  Lemma incl_clos_trans: (inclusion A R trans_clos).
    Red;Auto with sets.
  Qed.

  Lemma Acc_clos_trans: (x:A)(Acc A R x)->(Acc A trans_clos x).
    Induction 1.
    Intros x0 H0 H1.
    Apply Acc_intro.
    Intros y H2.
    Generalize H1 .
    Elim H2;Auto with sets.
    Intros x1 y0 z H3 H4 H5 H6 H7.
    Apply Acc_inv with y0 ;Auto with sets.
  Qed.

  Hints Resolve Acc_clos_trans.

  Lemma Acc_inv_trans: (x,y:A)(trans_clos y x)->(Acc A R x)->(Acc A R y).
  Proof.
    Induction 1;Auto with sets.
    Intros x0 y0 H0 H1.
    Apply Acc_inv with y0 ;Auto with sets.
  Qed.

  Theorem wf_clos_trans: (well_founded A R)  ->(well_founded A trans_clos).
  Proof.
    Unfold well_founded;Auto with sets.
  Qed.

End Wf_Transitive_Closure.
