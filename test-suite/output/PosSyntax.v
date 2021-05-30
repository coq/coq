Require Import PArith.
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
Fail Check 0%positive : positive.
Fail Check 0x0%positive : positive.
Fail Check 0x00%positive : positive.
Check 0x01%positive : positive.
Check 0x02%positive : positive.
Check 0xff%positive : positive.
Check 0xFF%positive : positive.
Check 0x01%xpositive : positive.
Check 0x02%xpositive : positive.
Check 0xff%xpositive : positive.
Check 0xFF%xpositive : positive.

(* Check hexadecimal printing *)
Open Scope hex_positive_scope.
Check 42%positive.
Check 1%positive.
Fail Check 0x0%positive : positive.
Fail Check 0x00%positive : positive.
Check 0x01%positive : positive.
Check 0x02%positive : positive.
Check 0xff%positive : positive.
Check 0xFF%positive : positive.
Fail Check 0x0 : positive.
Fail Check 0x00 : positive.
Check 0x01 : positive.
Check 0x02 : positive.
Check 0xff : positive.
Check 0xFF : positive.
Fail Check 0x0%xpositive : positive.
Fail Check 0x00%xpositive : positive.
Check 0x01%xpositive : positive.
Check 0x02%xpositive : positive.
Check 0xff%xpositive : positive.
Check 0xFF%xpositive : positive.
Close Scope hex_positive_scope.

Require Import Arith.
Check (1 + Pos.of_nat 11)%positive.
