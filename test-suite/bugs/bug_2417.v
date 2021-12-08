Parameter x y : nat.
Axiom H : x = y.
Hint Rewrite H : mybase.

Ltac bar base := autorewrite with base.

Tactic Notation "foo" ident(base) := autorewrite with base.

Goal x = 0.
  bar mybase.
  now_show (y = 0).
  Undo 2.
  foo mybase.
  now_show (y = 0).
Abort.
