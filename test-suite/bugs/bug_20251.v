Set Primitive Projections.
Set Printing Primitive Projection Parameters.

Record R (A:Type) := mk { p : A }.
Arguments p {_} _.

Axiom xbar : forall A,forall x: R A,  p x = p x.

Goal 0 = 0.
  Set Debug "tactic-unification".
  Fail apply xbar.
Abort.
