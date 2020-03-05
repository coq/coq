Fail Inductive list' (A:Set) : Set :=
| nil' : list' A
| cons' : A -> list' A -> list' (A*A).

(* Check printing of let-ins *)
#[universes(template)] Inductive foo (A : Type) (x : A) (y := x) := Foo.
Print foo.

(* Check where clause *)
Reserved Notation "x ** y" (at level 40, left associativity).
Inductive myprod A B :=
  mypair : A -> B -> A ** B
  where "A ** B" := (myprod A B) (only parsing).

Check unit ** bool.
