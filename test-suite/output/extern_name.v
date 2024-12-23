Hint Extern 1 True as Stdlib.Init.Nat.t => idtac "x" : db.
Print HintDb db.
Remove Hints Init.Nat.t : db.
Print HintDb db.
