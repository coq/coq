Fail Inductive list' (A:Set) : Set :=
| nil' : list' A
| cons' : A -> list' A -> list' (A*A).
  (* Note: There is a printing bug: information that the argument of [list']
     is a type was known from the parser (constrintern) but is not known
     from printing (constrextern) *)

(* Check printing of let-ins *)
#[universes(template)] Inductive foo (A : Type) (x : A) (y := x) := Foo.
Print foo.
