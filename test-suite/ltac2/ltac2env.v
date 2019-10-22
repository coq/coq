Require Import Ltac2.Ltac2.

Ltac2 get_opt o := match o with None => Control.throw Not_found | Some x => x end.

Goal True.
Proof.
(* Fails at runtime because not fully applied *)
Fail ltac1:(ltac2:(x |- ())).
(* Type mismatch: Ltac1.t vs. constr *)
Fail ltac1:(ltac2:(x |- pose $x)).
(* Check that runtime cast is OK *)
ltac1:(let t := ltac2:(x |- let c := (get_opt (Ltac1.to_constr x)) in pose $c) in t nat).
(* Type mismatch *)
Fail ltac1:(let t := ltac2:(x |- let c := (get_opt (Ltac1.to_constr x)) in pose $c) in t ident:(foo)).
Abort.
