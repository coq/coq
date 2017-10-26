Parameter Foo : Prop.
Axiom H : Foo.

Hint Resolve H : mybase.

Ltac foo base := eauto with base.

Tactic Notation "bar" ident(base) :=
  typeclasses eauto with base.

Goal Foo.
  progress foo mybase.
  Undo.
  progress bar mybase.
Qed.
