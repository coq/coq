Require Import FunInd.
Require  Vector.
Generalizable All Variables.

Definition f `{n:nat , u:Vector.t A n} := n.

Function f2 {A:Type} {n:nat} {v:Vector.t A n} : nat := n.

(* fails with "The reference A was not found in the current environment." *)
Function f3 `{n:nat , u:Vector.t A n} := u.
Check R_f3_complete.
