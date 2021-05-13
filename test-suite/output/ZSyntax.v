Require Import ZArith.
Check 32%Z.
Check (eq_refl : 0x2a%Z = 42%Z).
Check (fun f : nat -> Z => (f 0%nat + 0)%Z).
Check (fun x : positive => Zpos (xO x)).
Check (fun x : positive => (Zpos x + 1)%Z).
Check (fun x : positive => Zpos x).
Check (fun x : positive => Zneg (xO x)).
Check (fun x : positive => (Zpos (xO x) + 0)%Z).
Check (fun x : positive => (- Zpos (xO x))%Z).
Check (fun x : positive => (- Zpos (xO x) + 0)%Z).
Check (Z.of_nat 0 + 1)%Z.
Check (0 + Z.of_nat (0 + 0))%Z.
Check (Z.of_nat 0 = 0%Z).
Check 0x0%Z : Z.
Check 0x00%Z : Z.
Check 0x01%Z : Z.
Check 0x02%Z : Z.
Check 0xff%Z : Z.
Check 0xFF%Z : Z.
Check (-0x0)%Z : Z.
Check (-0x00)%Z : Z.
Check (-0x01)%Z : Z.
Check (-0x02)%Z : Z.
Check (-0xff)%Z : Z.
Check (-0xFF)%Z : Z.
Check 0x0%xZ : Z.
Check 0x00%xZ : Z.
Check 0x01%xZ : Z.
Check 0x02%xZ : Z.
Check 0xff%xZ : Z.
Check 0xFF%xZ : Z.
Check (-0x0)%xZ%Z : Z.
Check (-0x00)%xZ%Z : Z.
Check (-0x01)%xZ : Z.
Check (-0x02)%xZ : Z.
Check (-0xff)%xZ : Z.
Check (-0xFF)%xZ : Z.

(* Check hexadecimal printing *)
Open Scope hex_Z_scope.
Check 42%Z.
Check (-42)%Z.
Check 0%Z.
Check 42%xZ.
Check (-42)%xZ.
Check 0%xZ.
Check 0x0%Z : Z.
Check 0x00%Z : Z.
Check 0x01%Z : Z.
Check 0x02%Z : Z.
Check 0xff%Z : Z.
Check 0xFF%Z : Z.
Check (-0x0)%Z : Z.
Check (-0x00)%Z : Z.
Check (-0x01)%Z : Z.
Check (-0x02)%Z : Z.
Check (-0xff)%Z : Z.
Check (-0xFF)%Z : Z.
Check 0x0 : Z.
Check 0x00 : Z.
Check 0x01 : Z.
Check 0x02 : Z.
Check 0xff : Z.
Check 0xFF : Z.
Check 0x0%xZ : Z.
Check 0x00%xZ : Z.
Check 0x01%xZ : Z.
Check 0x02%xZ : Z.
Check 0xff%xZ : Z.
Check 0xFF%xZ : Z.
Check (-0x0)%xZ%Z : Z.
Check (-0x00)%xZ%Z : Z.
Check (-0x01)%xZ : Z.
Check (-0x02)%xZ : Z.
Check (-0xff)%xZ : Z.
Check (-0xFF)%xZ : Z.
Close Scope hex_Z_scope.

(* Submitted by Pierre Casteran *)
Require Import Arith.
Check (0 + Z.of_nat 11)%Z.
