Goal Type = Type.
  Fail match goal with |- ?x = ?x => idtac end.
Abort.

Goal Prop.
  Fail match goal with |- Type => idtac end.
Abort.

Goal Prop = Set.
  (* This should fail *)
 Fail match goal with |- ?x = ?x => idtac x end.
Abort.

Goal Type = Prop.
  (* This should fail *)
  Fail match goal with |- ?x = ?x => idtac end.
Abort.

Goal Type = Set.
  (* This should fail *)
  Fail match goal with |- ?x = ?x => idtac end.
Abort.
