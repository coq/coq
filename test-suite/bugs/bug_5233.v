(* Implicit arguments on type were missing for recursive records *)
Inductive foo {A : Type} : Type := { Foo : foo }.

(* Implicit arguments can be overidden *)
Inductive bar {A : Type} : Type := { Bar : @bar (A*A) }.
