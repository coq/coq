Require Import Ltac2.Ltac2.

Notation N x := True (only parsing).

Fail Ltac2 foo () := match! goal with [ |- N ?x ] => () end.
