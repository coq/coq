Require Import Program.

Program Definition foo : nat := ?[foo_nat] + _.
Next Obligation. exact 0. Qed.
Next Obligation. exact 1. Qed.

Fail Program Definition bar : nat := ?[foo_nat] + _.

Definition bar_obligation_1 := 0.

Fail Program Definition bar : nat := _.

Program Definition bar : nat := ?[bar_nat] + ?[bar_nat2].

Obligation bar_nat2 with constructor.
  idtac...
Defined.

Obligation bar_nat.
  exact 1.
Defined.

Check eq_refl : bar = 1.

Program Definition bar2 : nat := ?[bar_nat3] + ?bar_nat3.
Obligation bar_nat3.
  exact 2.
Defined.

Check eq_refl : bar2 = 4.
