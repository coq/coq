Set Universe Polymorphism.

Record Pred@{A} :=
  { car :> Type@{A}
  ; P : car -> Prop
  }.

Class All@{A} (A : Pred@{A}) :=
  { proof : forall (a : A), P A a
  }.

Record Pred_All@{A} : Type :=
  { P' :> Pred@{A}
  ; P'_All : All P'
  }.

Global Instance Pred_All_instance (A : Pred_All) : All A := P'_All A.

Definition Pred_All_proof {A : Pred_All} (a : A) : P A a.
Proof.
Fail solve[auto using proof]. (* Do not implicitly rely on TC resolution *)
solve[auto using proof, Pred_All_instance].
Abort.
