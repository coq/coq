From Stdlib Require Import QArith.
Open Scope Q_scope.
Check (eq_refl : 1.02 = 102 # 100).
Check 1.02e1.
Check 102 # 10.
Check 1.02e+03.
Check 1020.
Check 1.02e+02.
Check 102 # 1.
Check (eq_refl : 10.2e-1 = 1.02).
Check (eq_refl : -0.0001 = -1 # 10000).
Check (eq_refl : -0.50 = - 50 # 100).
Check 0.
Check 000.
Check 42.
Check 0x2a.
Check 1.23.
Check 0x1.23.
Check 0.0012.
Check 42e3.
Check 42e-3.
Open Scope hex_Q_scope.
Check (eq_refl : -0x1a = - 26 # 1).
Check (eq_refl : 0xb.2c = 2860 # 256).
Check (eq_refl : -0x1ae2 = -6882).
Check 0xb.2cp2.
Check 2860 # 64.
Check 0xb.2cp8.
Check 2860.
Check (eq_refl : -0xb.2cp-2 = -2860 # 1024).
Check 0x0.
Check 0x00.
Check 42.
Check 0x2a.
Check 1.23.
Check 0x1.23.
Check 0x0.0012.
Check 0x2ap3.
Check 0x2ap-3.
