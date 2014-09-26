Tactic Notation "test1" open_constr(t) ident(r):=
  pose t.
Tactic Notation "test2" constr(r) open_constr(t):=
  pose t.
Tactic Notation "test3" open_constr(t) constr(r):=
  pose t.

Goal True.
  test1 (1 + _) nat.
  test2 nat (1 + _).
  test3 (1 + _) nat.
  test3 (1 + _ : nat) nat.

