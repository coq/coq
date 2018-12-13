Set Warnings "+deprecated".

Notation bar := option (compat "8.7").

Definition foo (x: nat) : nat :=
  match x with
  | 0 => 0
  | S bar => bar
  end.
