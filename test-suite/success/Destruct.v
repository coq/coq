(* Submitted by Robert Schneck *)

Parameter A,B,C,D : Prop.
Axiom X : A->B->C/\D.

Lemma foo : A->B->C.
Proof.
Intros. 
NewDestruct X. (* Should find axiom X and should handle arguments of X *)
Assumption.
Assumption.
Assumption.
Qed.
