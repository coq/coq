Require Import Reals.
Open Scope R_scope.
Check (eq_refl : 1.02 = IZR 102 / IZR (Z.pow_pos 10 2)).
Check (eq_refl : 1.02e1 = IZR 102 / IZR (Z.pow_pos 10 1)).
Check (eq_refl : 1.02e+03 = IZR 102 * IZR (Z.pow_pos 10 1)).
Check (eq_refl : 1.02e+02 = IZR 102).
Check (eq_refl : 10.2e-1 = 1.02).
Check (eq_refl : -0.0001 = IZR (-1) / IZR (Z.pow_pos 10 4)).
Check (eq_refl : -0.5 = IZR (-5) / IZR (Z.pow_pos 10 1)).

Goal 254e3 = 2540 * 10 ^ 2.
ring.
Qed.

Require Import Psatz.

Goal 254e3 = 2540 * 10 ^ 2.
lra.
Qed.
