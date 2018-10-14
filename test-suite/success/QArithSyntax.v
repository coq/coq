Require Import QArith.
Open Scope Q_scope.
Check (eq_refl : 1.02 = 102 # 100).
Check (eq_refl : 1.02e1 = 102 # 10).
Check (eq_refl : 1.02e+03 = 1020).
Check (eq_refl : 1.02e+02 = 102 # 1).
Check (eq_refl : 10.2e-1 = 1.02).
Check (eq_refl : -0.0001 = -1 # 10000).
Check (eq_refl : -0.50 = - 50 # 100).
