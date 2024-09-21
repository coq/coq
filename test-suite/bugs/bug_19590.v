From Ltac2 Require Import Ltac2.

Definition a := 3.
Notation b := a.

Goal a = 3.
let ea := eval cbv delta [b] in a in change a with $ea.
(* Error: The reference b was not found in the current environment. *)
Abort.
