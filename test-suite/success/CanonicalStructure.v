(* Bug #1172 *)

Structure foo : Type := Foo {
   A : Set; Aopt := option A; unopt : Aopt -> A
}.

Canonical Structure unopt_nat := @Foo nat (fun _ => O).
