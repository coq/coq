Require Import TestSuite.admit.
Set Implicit Arguments.
Generalizable All Variables.

Polymorphic Record SpecializedCategory (obj : Type) := Build_SpecializedCategory' {
  Object :> _ := obj;
  Morphism' : obj -> obj -> Type;

  Identity' : forall o, Morphism' o o;
  Compose' : forall s d d', Morphism' d d' -> Morphism' s d -> Morphism' s d'
}.

Polymorphic Definition TypeCat : @SpecializedCategory Type
  := (@Build_SpecializedCategory' Type
                                  (fun s d => s -> d)
                                  (fun _ => (fun x => x))
                                  (fun _ _ _ f g => (fun x => f (g x)))).

Inductive GraphIndex := GraphIndexSource | GraphIndexTarget.
Polymorphic Definition GraphIndexingCategory : @SpecializedCategory GraphIndex.
Admitted.

Module success.
  Section SpecializedFunctor.
    Set Universe Polymorphism.
    Context `(C : @SpecializedCategory objC).
    Context `(D : @SpecializedCategory objD).
    Unset Universe Polymorphism.

    Polymorphic Record SpecializedFunctor
      := {
          ObjectOf' : objC -> objD;
          MorphismOf' : forall s d, C.(Morphism') s d -> D.(Morphism') (ObjectOf' s) (ObjectOf' d)
        }.
  End SpecializedFunctor.

  Polymorphic Definition UnderlyingGraph : SpecializedFunctor GraphIndexingCategory TypeCat.
  Admitted.
End success.

Module success2.
  Section SpecializedFunctor.
    Polymorphic Context `(C : @SpecializedCategory objC).
    Polymorphic Context `(D : @SpecializedCategory objD).

    Polymorphic Record SpecializedFunctor
      := {
          ObjectOf' : objC -> objD;
          MorphismOf' : forall s d, C.(Morphism') s d -> D.(Morphism') (ObjectOf' s) (ObjectOf' d)
        }.
  End SpecializedFunctor.

  Set Printing Universes.
  Polymorphic Definition UnderlyingGraph : SpecializedFunctor GraphIndexingCategory TypeCat.
  (* Toplevel input, characters 73-94:
Error:
The term "GraphIndexingCategory (* Top.563 *)" has type
 "SpecializedCategory (* Top.563 Set *) GraphIndex"
while it is expected to have type
 "SpecializedCategory (* Top.550 Top.551 *) ?7"
(Universe inconsistency: Cannot enforce Set = Top.551)). *)
  admit.
  Defined.
End success2.
