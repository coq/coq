Require Import Ltac2.Ltac2.

Ltac2 Eval
  let x := constr:(0) in
  Constr.pretype preterm:($x).
(* (* uncaught Not_found *) *)

Ltac2 Eval
  let x := constr:(0) in
  Constr.pretype preterm:(ltac2:(let y () := x in exact0 false y)).
(* (* anomaly unbound variable x *) *)

Notation "[ x ]" := ltac2:(exact0 false (fun ()  => Constr.pretype x)).

Check ltac2:(let y := constr:(0) in exact0 false (fun () => open_constr:([ $y ]))).
