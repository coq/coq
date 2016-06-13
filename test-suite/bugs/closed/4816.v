Section foo.
Polymorphic Universes A B.
Fail Constraint A <= B.
End foo.
(* gives an anomaly Universe undefined *)

Universes X Y.
Section Foo.
  Polymorphic Universes Z W.
  Polymorphic Constraint W < Z.

  Fail Definition bla := Type@{W}.
  Polymorphic Definition bla := Type@{W}.
  Section Bar.
    Fail Constraint X <= Z.
  End Bar.
End Foo.
