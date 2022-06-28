Definition x := 0.

#[export] Hint Unfold x : mybase.

Ltac autounfoldify base := autounfold with base.

Tactic Notation "autounfoldify_bis" ident(base) := autounfold with base.

Goal x = 0.
  progress autounfoldify mybase.
  Undo.
  progress autounfoldify_bis mybase.
  trivial.
Qed.
