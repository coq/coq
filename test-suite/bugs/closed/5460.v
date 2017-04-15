(* Bugs in computing dependencies in pattern-matching compilation *)

Inductive A := a1 | a2.
Inductive B := b.
Inductive C : A -> Type := c : C a1 | d : C a2.
Definition P (x : A) (y : C x) (z : B) : nat :=
  match z, x, y with
      | b, a1, c => 0
      | b, a2, d => 0
      | _, _, _ => 1
  end.
