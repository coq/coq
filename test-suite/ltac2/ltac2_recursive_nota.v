Require Import Ltac2.Ltac2.
Notation binder_act := ltac2:(exact eq_refl) (only parsing).
Notation binder x := (binder_act :> x = x) (only parsing).

#[local] Notation "'test{' x .. y } P" :=
  ((fun x => .. ((fun y => P), binder (fun y => I)) ..), binder (fun x => I))
    (at level 0, x binder, y binder, only parsing).

Check (test{(aa : nat) (bb : bool)} True).
