Require Import Ltac2.Ltac2.

(* cf bug #18556 *)

Ltac2 Type pair := [ C (int, int) ].

Ltac2 Eval C 0 0.
(* prints "C (0, 0)", should be "C 0 0" *)

Ltac2 Type pair' := [ C' (int * int) ].

Ltac2 Eval C' (0, 0).
(* prints "C' ((0, 0))", sound but over-parenthesized *)

Ltac2 Type ppair := [ D (pair) ].

Ltac2 Eval D (C 0 0).
