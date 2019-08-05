From Ltac2
Require Import Ltac2.

Notation "[ n ]" := ltac2:(Control.refine (fun n => constr:(n)))
  (only parsing).

Check (eq_refl : [ 0 ] = 0).
Check (eq_refl : [ nat ] = nat).

Notation "n .+2" := ltac2:(Control.refine (fun n => constr:(S (S n))))
  (at level 20, only parsing).

Definition four := Eval cbv in 2.+2.

Check (eq_refl : four = 4).

Notation ".< a | b .>" :=
  ltac2:(Control.refine (fun a => open_constr:(a + _ + b)))
  (only parsing).

Check .< 1 | 2 .>.
