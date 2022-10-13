Require Import Ltac2.Ltac2.
Module M.
  Ltac2 Type 'a foo := { a : 'a; b : 'a }.
End M.
Import M.

Ltac2 foo b := { a := (); b }.

Fail Ltac2 foo' (b:int) := { a := (); b }.

Ltac2 foo' b := { a := (); M.b }.
