Require Import TestSuite.admit.
Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.

Record SpecializedCategory (obj : Type) :=
  {
    Object :> _ := obj;
    Morphism : obj -> obj -> Type
  }.


Record > Category :=
  {
    CObject : Type;

    UnderlyingCategory :> @SpecializedCategory CObject
  }.

Record SpecializedFunctor `(C : @SpecializedCategory objC) `(D : @SpecializedCategory objD) :=
  {
    ObjectOf :> objC -> objD;
    MorphismOf : forall s d, C.(Morphism) s d -> D.(Morphism) (ObjectOf s) (ObjectOf d)
  }.

(* Replacing this with [Definition Functor (C D : Category) :=
SpecializedFunctor C D.] gets rid of the universe inconsistency. *)
Section Functor.
  Variable C D : Category.

  Definition Functor := SpecializedFunctor C D.
End Functor.

Record SpecializedNaturalTransformation `(C : @SpecializedCategory objC) `(D : @SpecializedCategory objD) (F G : SpecializedFunctor C D) :=
  {
    ComponentsOf :> forall c, D.(Morphism) (F c) (G c)
  }.

Definition FunctorProduct' `(F : Functor C D) : SpecializedFunctor C D.
admit.
Defined.

Definition TypeCat : @SpecializedCategory Type.
  admit.
Defined.


Definition CovariantHomFunctor `(C : @SpecializedCategory objC) : SpecializedFunctor C TypeCat.
  refine (Build_SpecializedFunctor C TypeCat
                                   (fun X : C => C.(Morphism) X X)
                                   _
         ); admit.
Defined.

Definition FunctorCategory `(C : @SpecializedCategory objC) `(D : @SpecializedCategory objD) : @SpecializedCategory (SpecializedFunctor C D).
  refine (@Build_SpecializedCategory _
                                     (SpecializedNaturalTransformation (C := C) (D := D))).
Defined.

Definition Yoneda `(C : @SpecializedCategory objC) : SpecializedFunctor C (FunctorCategory C TypeCat).
  match goal with
    | [ |- SpecializedFunctor ?C0 ?D0 ] =>
      refine (Build_SpecializedFunctor C0 D0
                                       (fun c => CovariantHomFunctor C)
                                       _
             )
  end;
  admit.
Defined.

Section FullyFaithful.
  Context `(C : @SpecializedCategory objC).
  Let TypeCatC := FunctorCategory C TypeCat.
  Let YC := (Yoneda C).
  Set Printing Universes.
  Check @FunctorProduct' C TypeCatC YC. (* Toplevel input, characters 0-37:
Error: Universe inconsistency. Cannot enforce Top.187 = Top.186 because
Top.186 <= Top.189 < Top.191 <= Top.187). *)
