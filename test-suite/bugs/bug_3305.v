Require Export Coq.Classes.RelationClasses.

Section defs.
  Variable A : Type.
  Variable lt : A -> A -> Prop.
  Context {ltso : StrictOrder lt}.

  Goal forall (a : A), lt a a -> False.
  Proof.
    intros a H.
    contradict (irreflexivity H).
  Qed.
End defs.
