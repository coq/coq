Goal Type = Type.
  match goal with |- ?x = ?x => idtac end.
Abort.

Goal Prop.
  Fail match goal with |- Type => idtac end.
Abort.

Goal Prop = Set.
  Fail match goal with |- ?x = ?x => idtac end.
Abort.

Goal Type = Prop.
  Fail match goal with |- ?x = ?x => idtac end.
Abort.

Goal Type = Set.
  Fail match goal with |- ?x = ?x => idtac end.
Abort.
