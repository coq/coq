Set Universe Polymorphism.

Axiom typ : Type.

Inductive S1a@{a} (A:typ@{a}) : Prop :=
with S1b (A:typ@{a}) : Prop :=
.
(*
Parameters should be syntactically the same for each inductive type.
Type "S1a" has parameters "(A : typ@{a})"
but type "S1b" has parameters "(A : typ@{a})".
*)
