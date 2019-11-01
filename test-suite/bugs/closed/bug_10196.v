From Ltac2 Require Import Ltac2.

(* true and false are valid constructors even though they are lowercase *)
Ltac2 Eval true.
Ltac2 Eval false.

(* Otherwise constructors have to be Uppercase *)
Ltac2 Type good_constructor := [Uppercased].
Ltac2 Type good_constructors := [Uppercased1 | Uppercased2].

Ltac2 Eval Uppercased2.

Fail Ltac2 Type bad_constructor := [ notUppercased ].
Fail Ltac2 Type bad_constructors := [ | notUppercased1 | notUppercased2 ].

Fail Ltac2 Eval notUppercased2.

(* And the same for open types*)
Ltac2 Type open_type := [ .. ].
Fail Ltac2 Type open_type ::= [ notUppercased ].
Ltac2 Type open_type ::= [ Uppercased ].

Fail Ltac2 Eval notUppercased.
Ltac2 Eval Uppercased.

Fail Ltac2 Type foo ::= [ | bar1 | bar2 ].
