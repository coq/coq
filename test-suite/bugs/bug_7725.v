Axioms T T' : Prop.

Ltac intuition_solver ::=
  match goal with
  | |- T' => shelve
  | _ => auto
  end.

Goal T -> T /\ T'.
  intuition.
  all:fail.
  Unshelve.
  match goal with |- T' => idtac end.
Abort.
