From Ltac2 Require Import Ltac2.

Ltac2 Type t := [..].
Ltac2 Type t ::= [A(int)].

(* t cannot be extended with two constructors with the same name *)
Fail Ltac2 Type t ::= [A(bool)].
Fail Ltac2 Type t ::= [B | B(bool)].

(* constructors cannot be shadowed in the same module *)
Fail Ltac2 Type s := [A].

(* constructors with the same name can be defined in distinct modules *)
Module Other.
  Ltac2 Type t ::= [A(bool)].
End Other.
Module YetAnother.
  Ltac2 Type t' := [A].
End YetAnother.
