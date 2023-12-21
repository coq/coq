Require TestSuite.relationclasses.

Class PreOrder (A : Type) (r : A -> A -> Type) : Type :=
{ refl : forall x, r x x }.

(* FAILURE 1 *)

#[universes(polymorphic)]
Section foo.
  Polymorphic Universes A.
  Polymorphic Context {A : Type@{A}} {rA : A -> A -> Prop} {PO : PreOrder A rA}.

  Fail Monomorphic Definition foo := PO.
End foo.


Module ILogic.

Set Universe Polymorphism.

(* Logical connectives *)
Class ILogic@{L} (A : Type@{L}) : Type := mkILogic
{
  lentails: A -> A -> Prop;
  lentailsPre:: RelationClasses.PreOrder lentails
}.


End ILogic.

Set Printing Universes.

(* There is still a problem if the class is universe polymorphic *)
#[universes(polymorphic)]
Section Embed_ILogic_Pre.
  Polymorphic Universes A T.
  Fail Monomorphic Context {A : Type@{A}} {ILA: ILogic.ILogic@{A} A}.

End Embed_ILogic_Pre.
