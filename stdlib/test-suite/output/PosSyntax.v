From Stdlib Require Import PArith.
Check 32%positive.
Check (eq_refl : 0x2a%positive = 42%positive).
Check (fun f : nat -> positive => (f 0%nat + 1)%positive).
Check (fun x : positive => xO x).
Check (fun x : positive => (x + 1)%positive).
Check (fun x : positive => x).
Check (fun x : positive => xI x).
Check (fun x : positive => (xO x + 1)%positive).
Check (Pos.of_nat 0 + 1)%positive.
Check (1 + Pos.of_nat (0 + 0))%positive.
Check (Pos.of_nat 1 = 1%positive).
Fail Check 0%positive.
Fail Check 0x0%positive.
Fail Check 0x00%positive.
Check 0x01%positive.
Check 0x02%positive.
Check 0xff%positive.
Check 0xFF%positive.
Check 0x01%xpositive.
Check 0x02%xpositive.
Check 0xff%xpositive.
Check 0xFF%xpositive.

(* Check hexadecimal printing *)
Open Scope hex_positive_scope.
Check 42%positive.
Check 1%positive.
Fail Check 0x0%positive.
Fail Check 0x00%positive.
Check 0x01%positive.
Check 0x02%positive.
Check 0xff%positive.
Check 0xFF%positive.
Fail Check 0x0.
Fail Check 0x00.
Check 0x01.
Check 0x02.
Check 0xff.
Check 0xFF.
Fail Check 0x0%xpositive.
Fail Check 0x00%xpositive.
Check 0x01%xpositive.
Check 0x02%xpositive.
Check 0xff%xpositive.
Check 0xFF%xpositive.
Close Scope hex_positive_scope.

From Stdlib Require Import Arith.
Check (1 + Pos.of_nat 11)%positive.
