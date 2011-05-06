Require Import ZArith.
Check 32%Z.
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

(* Submitted by Pierre Casteran *)
Require Import Arith.
Check (0 + Z.of_nat 11)%Z.
