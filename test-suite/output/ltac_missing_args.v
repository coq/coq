Ltac foo x := idtac x.
Ltac bar x := fun y _ => idtac x y.
Ltac baz := foo.
Ltac qux := bar.
Ltac mydo tac := tac ().
Ltac rec x := rec.

Goal True.
  Fail foo.
  Fail bar.
  Fail bar True.
  Fail baz.
  Fail qux.
  Fail mydo ltac:(fun _ _ => idtac).
  Fail let tac := (fun _ => idtac) in tac.
  Fail (fun _ => idtac).
  Fail rec True.
  Fail let rec tac x := tac in tac True.
Abort.
