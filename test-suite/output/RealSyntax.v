Require Import Reals.Rdefinitions.
Check 32%R.
Check (-31)%R.

Check 1.5_%R.
Check 1_.5_e1_%R.

Open Scope R_scope.

Check (eq_refl : 1.02 = IZR 102 / IZR (Z.pow_pos 10 2)).
Check (eq_refl : 1.02e1 = IZR 102 / IZR (Z.pow_pos 10 1)).
Check (eq_refl : 1.02e+03 = IZR 102 * IZR (Z.pow_pos 10 1)).
Check (eq_refl : 1.02e+02 = IZR 102).
Check (eq_refl : 10.2e-1 = 1.02).
Check (eq_refl : -0.0001 = IZR (-1) / IZR (Z.pow_pos 10 4)).
Check (eq_refl : -0.50 = IZR (-50) / IZR (Z.pow_pos 10 2)).
Check (eq_refl : -0x1a = - 26).
Check (eq_refl : 0xb.2c = IZR 2860 / IZR (Z.pow_pos 2 8)).
Check (eq_refl : -0x1ae2 = -6882).
Check (eq_refl : 0xb.2cp2 = IZR 2860 / IZR (Z.pow_pos 2 6)).
Check (eq_refl : 0xb.2cp8 = 2860).
Check (eq_refl : -0xb.2cp-2 = - IZR 2860 / IZR (Z.pow_pos 2 10)).

Require Import Reals.

Goal 254e3 = 2540 * 10 ^ 2.
ring.
Qed.

Require Import Psatz.

Goal 254e3 = 2540 * 10 ^ 2.
lra.
Qed.
