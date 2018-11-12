(* Implicit arguments on type were missing for recursive records *)
Inductive foo {A : Type} (a : A) : Type := { Foo : foo a }.
