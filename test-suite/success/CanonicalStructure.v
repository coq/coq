(* Bug #1172 *)

Structure foo : Type := Foo {
   A : Set; Aopt := option A; unopt : Aopt -> A
}.

Canonical Structure unopt_nat := @Foo nat (fun _ => O).

(* Granted wish #1187 *)

Record Silly (X : Set) : Set := mkSilly { x : X }.
Definition anotherMk := mkSilly.
Definition struct := anotherMk nat 3.
Canonical Structure struct.

(* Intertwinning canonical structures and delta-expansion *)
(* Assia's short example *)

Open Scope bool_scope.

Set Implicit Arguments.

Structure test_struct : Type := mk_test {dom :> Type; f : dom -> dom -> bool}.

Notation " x != y":= (f _ x y)(at level 10).

Canonical Structure bool_test := mk_test (fun x y => x || y).

Definition b := bool.

Check (fun x : b => x != x).
