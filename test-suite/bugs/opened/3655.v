Ltac bar x := pose x.
Tactic Notation "foo" open_constr(x) := bar x.
Class baz := { baz' : Type }.
Goal True.
(* Original error was an anomaly which is fixed; now, it succeeds but
   leaving an evar, while calling pose would not leave an evar, so I
   guess it is still a bug in the sense that the semantics of pose is
   not preserved *)
  foo baz'.
