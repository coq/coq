Require Import Ltac2.Ltac2.

Fail Ltac2 Eval
  let x := constr:(0) in
  Constr.pretype preterm:($x).
(* uncaught Not_found *)

Fail Ltac2 Eval
  let x := constr:(0) in
  Constr.pretype preterm:(ltac2:(let y () := x in exact0 false y)).
(* anomaly unbound variable x *)
