Fail Fixpoint rec a (x : nat) {struct x} :=
  let _ : nat := a (rec a) in
  0.

Fail Fixpoint rec a x {struct x} :=
  let _ :=
  match a with
  | 0 => 0
  | S n => rec a n
  end
  in
  0.
