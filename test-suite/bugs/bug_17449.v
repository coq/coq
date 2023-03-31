
Set Ltac Backtrace.

Ltac foo :=
  let c := open_constr:(fun x:nat => _) in
  pose (Prop:Prop) .

Goal True.
  Fail foo.
Abort.
