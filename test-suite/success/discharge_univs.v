Set Printing Universes.
Set Debug "inferCumul".
Module boxtop.

  Inductive box@{u} (A : Type@{u}) : Type@{u+1} := b : A -> box A.
About box.
End boxtop.
Module boxsec.
  Section Foo.
    Universe u.
    Context (A : Type@{u}).
    Inductive box : Type@{u+1} := b : A -> box.
  End Foo.
  About box.
End boxsec.

Section Foo.
  Universes u v w.
  Inductive box (A : Type@{u}) : Type@{u} := b : A -> box A.
  (* Constraint u <= v, v <= w.  *)
  Set Debug "inferCumul".
  Set Debug "univVariances".
  Definition foo := Type@{u}.

  Definition bar (A : Type@{w}) := foo.

End Foo.
Set Printing Universes.

About box.
About foo.
Print foo.
About bar.
Print bar.
Print foo.
Check foo@{0}.
