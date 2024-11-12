
(* To test PP of fixpoints *)
Require Import TestSuite.arith.
Check fix a(n: nat): n<5 -> nat :=
  match n return n<5 -> nat with
    | 0 => fun _ => 0
    | S n => fun h => S (a n (proj2 (Nat.succ_lt_mono _ _) (Nat.lt_lt_succ_r _ _ h)))
  end.
