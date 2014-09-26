Ltac bar x := pose x.
Tactic Notation "foo" open_constr(x) := bar x.
Class baz := { baz' : Type }.
Goal True.
  Fail foo baz'.
