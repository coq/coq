Require Import Ltac2.Ltac2.

(* This line is copied from https://coq.inria.fr/refman/proof-engine/ltac2.html *)
Notation "[ x ]" := ltac2:(let x := Ltac2.Constr.pretype x in exact $x) (only parsing).

Check [ 1 ].

Notation "<< y >>" := [ y + y ] (only parsing).

Check << 3 * 3 >>.
Check eq_refl : 18 = << 3 * 3 >>.
