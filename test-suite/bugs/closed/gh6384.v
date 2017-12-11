Theorem test (A:Prop) : A \/ A -> A.
  Fail intro H; destruct H as H.
  (* Error: Disjunctive/conjunctive introduction pattern expected. *)
  Fail intros H; destruct H as H.
Abort.
