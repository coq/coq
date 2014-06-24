Set Printing All.
Typeclasses eauto := debug.
Module success.
  Class foo := { F : nat }.
  Class bar := { B : nat }.
  Instance: foo := { F := 1 }.
  Instance: foo := { F := 0 }.
  Instance: bar := { B := 0 }.
  Definition BAZ := eq_refl : @F _ = @B _.
End success.

Module failure.
  Class foo := { F : nat }.
  Class bar := { B : nat }.
  Instance f0: foo := { F := 0 }.
  Instance f1: foo := { F := 1 }.
  Instance b0: bar := { B := 0 }.
  Fail Definition BAZ := eq_refl : @F _ = @B _.
  (* Toplevel input, characters 18-25:
Error:
The term "@eq_refl nat (@F f1)" has type "@eq nat (@F f1) (@F f1)"
while it is expected to have type "@eq nat (@F f1) (@B b0)"
(cannot unify "@F f1" and "@B b0"). *)
End failure.
