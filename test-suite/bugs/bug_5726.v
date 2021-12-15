Set Universe Polymorphism.
Set Printing Universes.

Module GlobalReference.

  Definition type' := Type.
  Notation type := type'.
  Check type@{Set}.

End GlobalReference.

Module TypeLiteral.

  Notation type := Type.
  Check type@{Set}.
  Check type@{Prop}.

End TypeLiteral.

Module ExplicitSort.
  Monomorphic Universe u.
  Notation foo := Type@{u}.
  Fail Check foo@{Set}.
  Fail Check foo@{u}.

  Notation bar := Type.
  Check bar@{u}.
End ExplicitSort.

Module PropNotationUnsupported.
  Notation foo := Prop.
  Fail Check foo@{Set}.
  Fail Check foo@{Type}.
End PropNotationUnsupported.
