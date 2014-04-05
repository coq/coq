(* Anomaly before 4a8950ec7a0d9f2b216e67e69b446c064590a8e9 *)

Require Import Recdef.

Function f_R (a: nat) {wf (fun x y: nat => False)  a}:Prop:=
  match a:nat with
    | 0 => True
    | (S y') => f_R y'
  end.
(* Anomaly: File "plugins/funind/recdef.ml", line 916, characters 13-19: Assertion failed.
Please report. *)
