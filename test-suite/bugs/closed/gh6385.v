Theorem test (A:Prop) : A \/ A -> A.
  Fail let H := idtac in intros H; destruct H as H'.
  (* Disjunctive/conjunctive introduction pattern expected. *)
  Fail let H' := idtac in intros H; destruct H as H'.
Abort.
