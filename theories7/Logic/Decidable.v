(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*i 	$Id$	 i*)

(** Properties of decidable propositions *)

Definition decidable := [P:Prop] P \/ ~P.

Theorem dec_not_not : (P:Prop)(decidable P) -> (~P -> False) -> P.
Unfold decidable; Tauto. 
Qed.

Theorem dec_True: (decidable True).
Unfold decidable; Auto.
Qed.

Theorem dec_False: (decidable False).
Unfold decidable not; Auto.
Qed.

Theorem dec_or: (A,B:Prop)(decidable A) -> (decidable B) -> (decidable (A\/B)).
Unfold decidable; Tauto. 
Qed.

Theorem dec_and: (A,B:Prop)(decidable A) -> (decidable B) ->(decidable (A/\B)).
Unfold decidable; Tauto. 
Qed.

Theorem dec_not: (A:Prop)(decidable A) -> (decidable ~A).
Unfold decidable; Tauto. 
Qed.

Theorem dec_imp: (A,B:Prop)(decidable A) -> (decidable B) ->(decidable (A->B)).
Unfold decidable; Tauto. 
Qed.

Theorem not_not : (P:Prop)(decidable P) -> (~(~P)) -> P.
Unfold decidable; Tauto. Qed.

Theorem not_or : (A,B:Prop) ~(A\/B) -> ~A /\ ~B.
Tauto. Qed.

Theorem not_and : (A,B:Prop) (decidable A) -> ~(A/\B) -> ~A \/ ~B.
Unfold decidable; Tauto. Qed.

Theorem not_imp : (A,B:Prop) (decidable A) -> ~(A -> B) -> A /\ ~B.
Unfold decidable;Tauto.
Qed.

Theorem imp_simp : (A,B:Prop) (decidable A) -> (A -> B) -> ~A \/ B.
Unfold decidable; Tauto.
Qed.

