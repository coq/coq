Program Definition test (a b : nat) : { x : nat | x = a + b } :=
  ((a + b) : { x : nat | x = a + b }).
Proof.
intros.
reflexivity.
Qed.

Print test.

Require Import List.

Program hd_opt (l : list nat) : { x : nat | x <> 0 } :=
  match l with
    nil => 1
    | a :: l => a
  end.
