Require Import ZArith Int63 Floats.

Open Scope float_scope.

Definition three := Eval compute in of_int63 3%int63.
Definition nine := Eval compute in of_int63 9%int63.

Check (eq_refl : sqrt nine = three).
Definition compute1 := Eval compute in sqrt nine.
Check (eq_refl : three = three).

Definition huge := Eval compute in ldexp one (1023)%Z.
Definition tiny := Eval compute in ldexp one (-1023)%Z.
Definition denorm := Eval compute in ldexp one (-1074)%Z.

Goal (Prim2SF (sqrt huge) = SF64sqrt (Prim2SF huge)).
  now compute.
Qed.

Goal (Prim2SF (sqrt tiny) = SF64sqrt (Prim2SF tiny)).
  now compute.
Qed.

Goal (Prim2SF (sqrt denorm) = SF64sqrt (Prim2SF denorm)).
  now compute.
Qed.

Check (eq_refl : sqrt neg_zero = neg_zero).
Check (eq_refl : sqrt zero = zero).
Check (eq_refl : sqrt one = one).
Check (eq_refl : sqrt (-one) = nan).
Check (eq_refl : sqrt infinity = infinity).
Check (eq_refl : sqrt neg_infinity = nan).
