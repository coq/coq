(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Author: Bruno Barras *)

Require Relation_Operators.
Require Relation_Definitions.
Require Transitive_Closure.

Section WfUnion.
  Variable A: Set.
  Variable R1,R2: (relation A).
  
 Notation Union := (union A R1 R2).

 Hints Resolve Acc_clos_trans wf_clos_trans.

Remark strip_commut: 
      (commut A R1 R2)->(x,y:A)(clos_trans A R1 y x)->(z:A)(R2 z y)
            ->(EX y':A | (R2 y' x) & (clos_trans A R1 z y')).
Proof.
 NewInduction 2 as [x y|x y z H0 IH1 H1 IH2]; Intros.
 Elim H with y x z ;Auto with sets;Intros x0 H2 H3.
 Exists x0;Auto with sets.

 Elim IH1 with z0 ;Auto with sets;Intros.
 Elim IH2 with x0 ;Auto with sets;Intros.
 Exists x1;Auto with sets.
 Apply t_trans with x0; Auto with sets.
Qed.


  Lemma Acc_union:  (commut A R1 R2)->((x:A)(Acc A R2 x)->(Acc A R1 x))
                         ->(a:A)(Acc A R2 a)->(Acc A Union a).
Proof.
 NewInduction 3 as [x H1 H2].
 Apply Acc_intro;Intros.
 Elim H3;Intros;Auto with sets.
 Cut (clos_trans A  R1 y x);Auto with sets.
 ElimType (Acc A (clos_trans A R1) y);Intros.
 Apply Acc_intro;Intros.
 Elim H8;Intros.
 Apply H6;Auto with sets.
 Apply t_trans with x0 ;Auto with sets.

 Elim strip_commut with x x0 y0 ;Auto with sets;Intros.
 Apply Acc_inv_trans with x1 ;Auto with sets.
 Unfold union .
 Elim H11;Auto with sets;Intros.
 Apply t_trans with y1 ;Auto with sets.

 Apply (Acc_clos_trans A).
 Apply Acc_inv with x ;Auto with sets.
 Apply H0.
 Apply Acc_intro;Auto with sets.
Qed.


  Theorem wf_union:  (commut A R1 R2)->(well_founded A R1)->(well_founded A R2)
                  ->(well_founded A Union).
Proof.
 Unfold well_founded .
 Intros.
 Apply Acc_union;Auto with sets.
Qed.

End WfUnion.
