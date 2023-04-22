Require Import Ltac2.Ltac2.

Ltac2 foo x y z :=
  let a := constr:($x + ltac:(exact $y)) in
  constr:($a + ltac2:(let y := z in exact (S $y))).

Set Printing Ltac2 Extension Used Variables.

Print foo.

Ltac2 Eval foo constr:(0) constr:(1) constr:(2).
