Sort s.
Sort s'.

Fail Check fun (A:Type@{s|Set}) => A : Type@{s'|_}.

Fail Check fun (A:Type@{s|Set}) => A : Type.

Fail Check fun (A:Set) => A : Type@{s|_}.

Check fun (A:Type@{s|Set}) => A : Type@{s|_}.

Section S.
  Sort S1.
  Set Universe Polymorphism.
  Sort S2.

  Axiom foo : Type@{S1|Set} -> Type@{S2|Set}.
  Check foo.

End S.

About foo.
Set Printing Universes.
About foo.

Check foo : _ -> SProp.
Check foo : _ -> Set.

Fail Check foo : SProp -> _.
Fail Check foo : Set -> _.
Check foo : Type@{S1|Set} -> Set.
