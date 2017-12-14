Theorem test (A:Prop) : A \/ A -> A.
  Fail intros H; destruct H as H.
  (* Cannot coerce to a disjunctive/conjunctive pattern. *)
  Fail intro H; destruct H as H.
  (* Disjunctive/conjunctive introduction pattern expected. *)
  Fail let H := fresh in intro H; destruct H as H.
  (* Cannot coerce to a disjunctive/conjunctive pattern. *)
  Fail let H := fresh in intros H; destruct H as H.
  (* Cannot coerce to a disjunctive/conjunctive pattern. *)
  Fail let H := idtac in intros H; destruct H as H.
  (* Ltac variable H is bound to <tactic closure> which cannot be
coerced to an introduction pattern. *)
  Fail let H := idtac in intros H; destruct H as H'.
  (* Disjunctive/conjunctive introduction pattern expected. *)
  Fail let H' := idtac in intros H; destruct H as H'.
(* Ltac variable H' is bound to <tactic closure> which cannot
be coerced to an introduction pattern. *)
Abort.
