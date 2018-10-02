Goal False.

intuition
  match goal with
  | |- _ => idtac " foo"
  end.

  lazymatch goal with _ => idtac end.
  match goal with _ => idtac end.
  unshelve lazymatch goal with _ => idtac end.
  unshelve match goal with _ => idtac end.
  unshelve (let x := I in idtac).
Abort.

Require Import ssreflect.

Goal True.
match goal with _ => idtac end => //.
Qed.
