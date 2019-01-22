Require Coq.Classes.RelationClasses.

Class PreOrder (A : Type) (r : A -> A -> Type) : Type :=
{ refl : forall x, r x x }.

(* FAILURE 1 *)

Section foo.
  Polymorphic Universes A.
  Polymorphic Context {A : Type@{A}} {rA : A -> A -> Prop} {PO : PreOrder A rA}.

  Definition foo := PO.
End foo.
Check foo@{_}. (* foo takes a universe even though it's marked monomorphic *)

Module ILogic.

Set Universe Polymorphism.

(* Logical connectives *)
Class ILogic@{L} (A : Type@{L}) : Type := mkILogic
{
  lentails: A -> A -> Prop;
  lentailsPre:> RelationClasses.PreOrder lentails
}.


End ILogic.

Set Printing Universes.

(* There is stil a problem if the class is universe polymorphic *)
Section Embed_ILogic_Pre.
  Polymorphic Universes A T.
  Fail Context {A : Type@{A}} {ILA: ILogic.ILogic@{A} A}.

End Embed_ILogic_Pre.
