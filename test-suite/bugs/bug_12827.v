Existing Class True.
Existing Instance I.

(* ltac1 exact works *)
Goal True.
  exact _.
Qed.

Require Import Ltac2.Ltac2.
Require Import Ltac2.Notations.

Goal True.
  exact _.
  (* was: Error: Cannot infer this placeholder of type "True" (no type class instance
found).
   *)
Qed.
