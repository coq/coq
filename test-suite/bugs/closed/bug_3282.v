(* Check let-ins in fix and Fixpoint *)

Definition foo := fix f (m : nat) (o := true) (n : nat) {struct n} :=
  match n with 0 => 0 | S n' => f 0 n' end.

Fixpoint f (m : nat) (o := true) (n : nat) {struct n} :=
  match n with 0 => 0 | S n' => f 0 n' end.
