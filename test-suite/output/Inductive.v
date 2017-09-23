Fail Inductive list' (A:Set) : Set :=
| nil' : list' A
| cons' : A -> list' A -> list' (A*A).

(* Check printing of let-ins *)
Inductive foo (A : Type) (x : A) (y := x) := Foo.
Print foo.
