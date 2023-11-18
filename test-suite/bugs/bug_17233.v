Require Import Ltac2.Ltac2.

(* exact0 at the time of the bug, with eexact part removed for simplicity *)
Ltac2 exact0 c :=
  Control.enter (fun _ =>
      Control.with_holes c (fun c => Control.refine (fun _ => c))).

Ltac2 Eval
  let x := constr:(0) in
  Constr.pretype preterm:($x).
(* (* uncaught Not_found *) *)

Ltac2 Eval
  let x := constr:(0) in
  Constr.pretype preterm:(ltac2:(let y () := x in exact0 y)).
(* (* anomaly unbound variable x *) *)

Notation "[ x ]" := ltac2:(exact0 (fun ()  => Constr.pretype x)).

Check ltac2:(let y := constr:(0) in exact0 (fun () => open_constr:([ $y ]))).
