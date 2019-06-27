#[universes(polymorphic)]
Section foo.
Polymorphic Universes A B.
Fail Constraint A <= B.
End foo.
(* gives an anomaly Universe undefined *)

Universes X Y.
#[universes(polymorphic)]
Section Foo.
  Polymorphic Universes Z W.
  Polymorphic Constraint W < Z.

  Fail Definition bla := Type@{W}.
  Polymorphic Definition bla := Type@{W}.
  #[universes(polymorphic)]
  Section Bar.
    Fail Constraint X <= Z.
  End Bar.
End Foo.

Require Coq.Classes.RelationClasses.

Class PreOrder (A : Type) (r : A -> A -> Type) : Type :=
{ refl : forall x, r x x }.

#[universes(polymorphic)]
Section qux.
  Polymorphic Universes A.
  #[universes(polymorphic)]
  Section bar.
    Fail Context {A : Type@{A}} {rA : A -> A -> Prop} {PO : PreOrder A rA}.
  End bar.
End qux.
