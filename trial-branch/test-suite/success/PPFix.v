
(* To test PP of fixpoints *)
Require Import Arith.
Check fix a(n: nat): n<5 -> nat :=
  match n return n<5 -> nat with
    | 0 => fun _ => 0
    | S n => fun h => S (a n (lt_S_n _ _ (lt_S _ _ h)))
  end.

