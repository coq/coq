(* Test support of let-in in arity of inductive types *)

Inductive Foo : let X := Set in X :=
| I : Foo.

Definition foo (x : Foo) : bool :=
  match x with
  I => true
  end.
