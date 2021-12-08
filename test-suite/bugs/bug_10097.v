From Ltac2 Require Import Ltac2.

(* #10097 *)
Ltac2 Type s := [X(int)].
Fail Ltac2 Type s.
Fail Ltac2 Type s := [].

Ltac2 Type r := [..].
Fail Ltac2 Type r := [].

Module Other.
  Ltac2 Type s.
  Ltac2 Type r := [].
End Other.
