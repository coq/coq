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

(* Simplification of bug 711 *)

Parameter f:true=false.
Goal let p=f in True.
Intro p.
LetTac b:=true.
(* Check that it doesn't fail with an anomaly *)
(* Ultimately, adapt destruct to make it succeeding *)
Try NewDestruct b.
