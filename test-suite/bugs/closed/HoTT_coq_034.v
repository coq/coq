Module Short.
  Set Universe Polymorphism.
  Inductive relevant (A : Type) (B : Type) : Prop := .
  Section foo.
    Variables A B : Type.
    Definition foo := prod (relevant A B) A.
  End foo.

  Section bar.
    Variable A : Type.
    Variable B : Type.
    Definition bar := prod (relevant A B) A.
  End bar.

  Set Printing Universes.
  Check bar nat Set : Set. (* success *)
  Check foo nat Set : Set. (* Toplevel input, characters 6-17:
Error:
The term "foo (* Top.303 Top.304 *) nat Set" has type
"Type (* Top.304 *)" while it is expected to have type
"Set" (Universe inconsistency: Cannot enforce Top.304 = Set because Set
< Top.304)). *)
End Short.

Section Long.
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
    Check @FunctorProduct' C TypeCatC (Yoneda C).
    (* Toplevel input, characters 35-43:
Error:
In environment
objC : Type (* Top.186 *)
C : SpecializedCategory (* Top.185 Top.186 *) objC
TypeCatC := FunctorCategory (* Top.187 Top.185 Top.189 Top.186 Top.191
              Top.192 *) C TypeCat (* Top.193 Top.192 Top.195 Top.191 *)
         : SpecializedCategory (* Top.189 Top.187 *)
             (SpecializedFunctor (* Top.192 Top.186 Top.191 Top.185 *) C
                TypeCat (* Top.193 Top.192 Top.195 Top.191 *))
YC := Yoneda (* Top.197 Top.198 Top.185 Top.186 Top.201 Top.202 Top.203
        Top.204 Top.185 Top.206 *) C
   : SpecializedFunctor (* Top.202 Top.186 Top.203 Top.185 *) C
       (FunctorCategory (* Top.203 Top.185 Top.202 Top.186 Top.197 Top.198 *)
          C TypeCat (* Top.185 Top.198 Top.204 Top.197 *))
The term
 "Yoneda (* Top.225 Top.226 Top.227 Top.186 Top.229 Top.230 Top.231 Top.232
    Top.185 Top.234 *) C" has type
 "SpecializedFunctor (* Top.230 Top.228 Top.231 Top.233 *) C
    (FunctorCategory (* Top.231 Top.233 Top.230 Top.228 Top.225 Top.226 *) C
       TypeCat (* Top.227 Top.226 Top.232 Top.225 *))"
while it is expected to have type
 "Functor (* Top.216 Top.219 Top.217 Top.220 *) C TypeCatC"
(Universe inconsistency: Cannot enforce Top.230 = Top.217 because Top.217
<= Top.227 < Top.225 <= Top.231 <= Top.230)).
     *)
End Long.
