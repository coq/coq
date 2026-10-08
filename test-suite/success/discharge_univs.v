Set Printing Universes.
Module boxtop.
  Inductive box@{u} (A : Type@{u}) : Type@{u+1} := b : A -> box A.
  Check box@{0}.
End boxtop.
Module boxsec.
  Section Foo.
    Universe u.
    Context (A : Type@{u}).
    Inductive box : Type@{u+1} := b : A -> box.
  End Foo.
  Check box@{0}.
End boxsec.

Section Foo.
  Universes u v w.
  Inductive box (A : Type@{u}) : Type@{u} := b : A -> box A.
  Definition foo := Type@{u}.

  Definition bar (A : Type@{w}) := foo.
  Constraint u <= v, v <= w.
  Definition baz (A : Type@{w}) := foo.

End Foo.
Check box@{0}.
Check foo@{0}.
Check bar@{0 0}.
Fail Check baz@{1 0 1}.
Check baz@{0 1 2}.
