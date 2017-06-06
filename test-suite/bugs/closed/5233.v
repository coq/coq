(* Implicit arguments on type were missing for recursive records *)
Inductive foo {A : Type} : Type := { Foo : foo }.
