From Stdlib Require Import Reals.Rdefinitions.
Check 32%R.
Check (-31)%R.

Check 1.5_%R.
Check 1_.5_e1_%R.

Open Scope R_scope.

Check (eq_refl : 1.02 = IZR 102 / IZR (Z.pow_pos 10 2)).
Check 1.02e1.
Check IZR 102 / IZR (Z.pow_pos 10 1).
Check 1.02e+03.
Check IZR 102 * IZR (Z.pow_pos 10 1).
Check 1.02e+02.
Check IZR 102.
Check 10.2e-1.
Check 1.02.
Check (eq_refl : -0.0001 = IZR (-1) / IZR (Z.pow_pos 10 4)).
Check (eq_refl : -0.50 = IZR (-50) / IZR (Z.pow_pos 10 2)).
Check (eq_refl : -0x1a = - 26).
Check (eq_refl : 0xb.2c = IZR 2860 / IZR (Z.pow_pos 2 8)).
Check (eq_refl : -0x1ae2 = -6882).
Check 0xb.2cp2.
Check IZR 2860 / IZR (Z.pow_pos 2 6).
Check 0xb.2cp8.
Check 2860.
Check -0xb.2cp-2.
Check - (IZR 2860 / IZR (Z.pow_pos 2 10)).
Check 0.
Check 000.
Check 42.
Check 0x2a.
Check 1.23.
Check 0x1.23.
Check 0.0012.
Check 42e3.
Check 42e-3.

Open Scope hex_R_scope.

Check 0x0.
Check 0x000.
Check 42.
Check 0x2a.
Check 1.23.
Check 0x1.23.
Check 0x0.0012.
Check 0x2ap3.
Check 0x2ap-3.

Close Scope hex_R_scope.

From Stdlib Require Import Reals.

Goal 254e3 = 2540 * 10 ^ 2.
ring.
Qed.

From Stdlib Require Import Psatz.

Goal 254e3 = 2540 * 10 ^ 2.
lra.
Qed.
