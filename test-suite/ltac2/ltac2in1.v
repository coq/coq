Require Import Ltac2.Ltac2.

Import Constr.Unsafe.

(* manual Ltac1.lambda wrapping *)
Ltac add1 :=
  ltac2val:(Ltac1.lambda (fun y =>
    let y := Option.get (Ltac1.to_constr y) in
    let y := make (App constr:(S) [|y|]) in
    Ltac1.of_constr y)).

(* automatic Ltac1.lambda wrapping
   also check that it's done in the right order *)
Ltac add1' :=
  ltac2val:(y z |-
    let y := Option.get (Ltac1.to_constr y) in
    let y := make (App constr:(S) [|y|]) in
    Ltac1.of_constr y).

Set Default Proof Mode "Classic".

Goal True.
  let z := constr:(0) in
  let v := add1 z in
  constr_eq v 1.

  let a := constr:(0) in
  let v := add1' a 2 in
  constr_eq v 1.

  (* currying works *)
  let a := constr:(0) in
  let v := add1' a in
  let v' := v 2 in
  constr_eq v' 1.

  (* check order of arguments *)
  Fail let a := constr:(0) in
  let v := add1' 2 a in
  constr_eq v 1.

  (* printer doesn't anomaly *)
  let v := add1' in
  idtac v.

Abort.

(* With ltac2:(x) this would succeed without warning
   "this expression should have type unit but has type constr"
   because ltac2:(x) only checks that x has type unifiable with unit.
   It's not a big problem as the constr gets discarded by ltac2:()
   so we just get an incomplete warning (maybe fixed in the future).

   With ltac2val such a weak check would produce runtime anomalies.
 *)
Fail Ltac2 bad x :=
  let c1 := constr:(ltac:(ltac2val:(x))) in
  let c2 := constr:($x) in
  ().
