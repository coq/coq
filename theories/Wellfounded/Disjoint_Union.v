(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(** Author: Cristina Cornes
    From : Constructing Recursion Operators in Type Theory                 
           L. Paulson  JSC (1986) 2, 325-355 *) 

Require Relation_Operators.

Section Wf_Disjoint_Union.
Variable A,B:Set.
Variable leA: A->A->Prop.
Variable leB: B->B->Prop.

Syntactic Definition Le_AsB := (le_AsB A B leA leB).

Lemma acc_A_sum: (x:A)(Acc A leA x)->(Acc A+B Le_AsB (inl A B x)).
Proof.
 Induction 1;Intros.
 Apply Acc_intro;Intros.
 Inversion_clear H2.
 Auto with sets.
Qed.

Lemma acc_B_sum: (well_founded A leA) ->(x:B)(Acc B leB x)
                        ->(Acc A+B Le_AsB (inr A B x)).
Proof.
 Induction 2;Intros.
 Apply Acc_intro;Intros.
 Inversion_clear H3;Auto with sets.
 Apply acc_A_sum;Auto with sets.
Qed.


Lemma wf_disjoint_sum:
 (well_founded A leA) 
    -> (well_founded B leB) -> (well_founded A+B Le_AsB).
Proof.
 Intros.
 Unfold well_founded .
 Induction a.
 Intro a0.
 Apply (acc_A_sum a0).
 Apply (H a0).

 Intro b.
 Apply (acc_B_sum H b).
 Apply (H0 b).
Qed.

End Wf_Disjoint_Union.
