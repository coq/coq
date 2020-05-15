Require Import QArith.
Open Scope Q_scope.
Check (eq_refl : 1.02 = 102 # 100).
Check (eq_refl : 1.02e1 = 102 # 10).
Check (eq_refl : 1.02e+03 = 1020).
Check (eq_refl : 1.02e+02 = 102 # 1).
Check (eq_refl : 10.2e-1 = 1.02).
Check (eq_refl : -0.0001 = -1 # 10000).
Check (eq_refl : -0.50 = - 50 # 100).
Check (eq_refl : -0x1a = - 26 # 1).
Check (eq_refl : 0xb.2c = 2860 # 256).
Check (eq_refl : -0x1ae2 = -6882).
Check (eq_refl : 0xb.2cp2 = 2860 # 64).
Check (eq_refl : 0xb.2cp8 = 2860).
Check (eq_refl : -0xb.2cp-2 = -2860 # 1024).
