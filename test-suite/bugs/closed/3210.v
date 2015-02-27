(* Test support of let-in in arity of inductive types *)

Inductive Foo : let X := Set in X :=
| I : Foo.

Definition foo (x : Foo) : bool :=
  match x with
  I => true
  end.

Definition foo' (x : Foo) : x = x.
case x.
match goal with |- I = I => idtac end. (* check form of the goal *)
Undo 2.
elim x.
match goal with |- I = I => idtac end. (* check form of the goal *)
Undo 2.
induction x.
match goal with |- I = I => idtac end. (* check form of the goal *)
Undo 2.
destruct x.
match goal with |- I = I => idtac end. (* check form of the goal *)
