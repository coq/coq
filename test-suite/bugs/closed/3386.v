Unset Strict Universe Declaration.
Set Universe Polymorphism.
Set Printing Universes.
Record Cat := { Obj :> Type }.
Definition set_cat := {| Obj := Type |}.
Goal Type@{i} = Type@{j}.
Proof.
  (* 1 subgoals
, subgoal 1 (ID 3)

  ============================
   Type@{Top.368} = Type@{Top.370}
(dependent evars:) *)
  Fail change Type@{i} with (Obj set_cat@{i}). (* check that it fails *)
  try change Type@{i} with (Obj set_cat@{i}). (* check that it's not an anomaly *)
(* Anomaly: Uncaught exception Invalid_argument("Array.iter2", _).
Please report. *)
