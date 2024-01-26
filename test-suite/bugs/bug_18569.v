
Polymorphic Inductive foo@{u} (A:Type@{u}) : Set := .

Inductive bar : Prop := C : foo bar -> bar.

(* NB: foo is not declared cumulative *)
Check C : foo@{Set} bar -> bar.
