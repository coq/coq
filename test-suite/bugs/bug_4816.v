#[universes(polymorphic)]
Section foo.
Polymorphic Universes A B.
Fail Monomorphic Constraint A <= B.
End foo.
(* gives an anomaly Universe undefined *)

Universes X Y.
#[universes(polymorphic)]
Section Foo.
  Polymorphic Universes Z W.
  Polymorphic Constraint W < Z.

  Fail Monomorphic Definition bla := Type@{W}.
  Polymorphic Definition bla := Type@{W}.
  #[universes(polymorphic)]
  Section Bar.
    Fail Monomorphic Constraint X <= Z.
  End Bar.
End Foo.

Axiom PreOrder : forall (A : Type) (r : A -> A -> Type), Type.

#[universes(polymorphic)]
Section qux.
  Polymorphic Universes A.
  #[universes(polymorphic)]
  Section bar.
    Fail Monomorphic Context {A : Type@{A}} {rA : A -> A -> Prop} {PO : PreOrder A rA}.
  End bar.
End qux.
