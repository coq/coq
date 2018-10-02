Tactic Notation "epose" open_constr(a) :=
  let a' := fresh in
  pose a as a'.
Tactic Notation "epose2" open_constr(a) tactic3(tac) :=
  let a' := fresh in
  pose a as a'.
Goal True.
  epose _. Undo.
  epose2 _ idtac.
