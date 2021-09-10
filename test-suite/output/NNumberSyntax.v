Require Import NArith.
Check 32%N.
Check (eq_refl : 0x2a%N = 42%N).
Check (fun f : nat -> N => (f 0%nat + 0)%N).
Check (fun x : positive => Npos (xO x)).
Check (fun x : positive => (Npos x + 1)%N).
Check (fun x : positive => Npos x).
Check (fun x : positive => Npos (xI x)).
Check (fun x : positive => (Npos (xO x) + 0)%N).
Check (N.of_nat 0 + 1)%N.
Check (0 + N.of_nat (0 + 0))%N.
Check (N.of_nat 0 = 0%N).
Check 0x00%N : N.
Check 0x01%N : N.
Check 0x02%N : N.
Check 0xff%N : N.
Check 0xFF%N : N.
Check 0x00%xN : N.
Check 0x01%xN : N.
Check 0x02%xN : N.
Check 0xff%xN : N.
Check 0xFF%xN : N.

(* Check hexadecimal printing *)
Open Scope hex_N_scope.
Check 42%N.
Check 0%N.
Check 42%xN.
Check 0%xN.
Check 0x00%N : N.
Check 0x01%N : N.
Check 0x02%N : N.
Check 0xff%N : N.
Check 0xFF%N : N.
Check 0x0%xN : N.
Check 0x00%xN : N.
Check 0x01%xN : N.
Check 0x02%xN : N.
Check 0xff%xN : N.
Check 0xFF%xN : N.
Check 0x0 : N.
Check 0x00 : N.
Check 0x01 : N.
Check 0x02 : N.
Check 0xff : N.
Check 0xFF : N.
Close Scope hex_N_scope.

Require Import Arith.
Check (0 + N.of_nat 11)%N.
