(* Check all variables are different in a Context *)
Ltac X := match goal with
          | x:_,x:_ |- _ => apply x
          end.
Goal True -> True -> True.
intros.
Fail X.
