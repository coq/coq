Require Import FunInd.

Function test {T} (v : T) (x : nat) : nat :=
  match x with
  | 0 => 0
  | S x' => test v x'
  end.

Check R_test_complete.
