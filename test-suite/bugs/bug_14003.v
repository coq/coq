Require Import Ltac2.Ltac2.

Module Foo.

Ltac2 foo := ().
Ltac2 Type bar := [ BAR ].
Ltac2 Type quz := [ .. ].
Ltac2 Type quz ::= [ QUZ ].

End Foo.

Import Foo.

(* Check that redeclaration checks are based on absolute names *)

Ltac2 foo := ().
Ltac2 Type bar := [ ].
Ltac2 Type qux := [ BAR ].
Ltac2 Type quz ::= [ QUZ ].
