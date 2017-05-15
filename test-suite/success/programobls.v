Require Import Program.

Program Definition foo : nat := ?[foo_nat] + _.
Next Obligation. exact 0. Qed.
Next Obligation. exact 1. Qed.

Fail Program Definition bar : nat := ?[foo_nat] + _.

Definition bar_obligation_1 := 0.

Fail Program Definition bar : nat := _.
