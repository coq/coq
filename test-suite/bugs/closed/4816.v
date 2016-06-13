Require Coq.Classes.RelationClasses.

Class PreOrder (A : Type) (r : A -> A -> Type) : Type :=
{ refl : forall x, r x x }.

Section foo.
  Polymorphic Universes A.
  Section bar.
    Fail Context {A : Type@{A}} {rA : A -> A -> Prop} {PO : PreOrder A rA}.
  End bar.
End foo.