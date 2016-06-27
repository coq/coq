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

Require Coq.Classes.RelationClasses.

Class PreOrder (A : Type) (r : A -> A -> Type) : Type :=
{ refl : forall x, r x x }.

Section qux.
  Polymorphic Universes A.
  Section bar.
    Fail Context {A : Type@{A}} {rA : A -> A -> Prop} {PO : PreOrder A rA}.
  End bar.
End qux.
