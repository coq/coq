Require Import TestSuite.admit.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.
Set Universe Polymorphism.

Delimit Scope object_scope with object.
Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Delimit Scope functor_scope with functor.

Local Open Scope category_scope.

Record SpecializedCategory (obj : Type) :=
  {
    Object :> _ := obj;
    Morphism : obj -> obj -> Type;

    Compose : forall s d d', Morphism d d' -> Morphism s d -> Morphism s d'
  }.

Bind Scope category_scope with SpecializedCategory.
Bind Scope object_scope with Object.
Bind Scope morphism_scope with Morphism.

Arguments Object {obj%type} C%category / : rename.
Arguments Morphism {obj%type} !C%category s d : rename. (* , simpl nomatch. *)
Arguments Compose {obj%type} [!C%category s%object d%object d'%object] m1%morphism m2%morphism : rename.

Record Category := {
  CObject : Type;

  UnderlyingCategory :> @SpecializedCategory CObject
}.

Definition GeneralizeCategory `(C : @SpecializedCategory obj) : Category.
  refine {| CObject := C.(Object) |}; auto. (* Changing this [auto] to [assumption] removes the universe inconsistency. *)
Defined.

Coercion GeneralizeCategory : SpecializedCategory >-> Category.

Record SpecializedFunctor
       `(C : @SpecializedCategory objC)
       `(D : @SpecializedCategory objD)
  := {
      ObjectOf :> objC -> objD;
      MorphismOf : forall s d, C.(Morphism) s d -> D.(Morphism) (ObjectOf s) (ObjectOf d)
    }.

Section Functor.
  Context (C D : Category).

  Definition Functor := SpecializedFunctor C D.
End Functor.

Bind Scope functor_scope with SpecializedFunctor.
Bind Scope functor_scope with Functor.

Arguments SpecializedFunctor {objC} C {objD} D.
Arguments Functor C D.
Arguments ObjectOf {objC%type C%category objD%type D%category} F%functor c%object : rename, simpl nomatch.
Arguments MorphismOf {objC%type} [C%category] {objD%type} [D%category] F%functor [s%object d%object] m%morphism : rename, simpl nomatch.

Section FunctorComposition.
  Context `(B : @SpecializedCategory objB).
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Context `(E : @SpecializedCategory objE).

  Definition ComposeFunctors (G : SpecializedFunctor D E) (F : SpecializedFunctor C D) : SpecializedFunctor C E
    := Build_SpecializedFunctor C E
                                (fun c => G (F c))
                                (fun _ _ m => G.(MorphismOf) (F.(MorphismOf) m)).
End FunctorComposition.

Record SpecializedNaturalTransformation
       `{C : @SpecializedCategory objC}
       `{D : @SpecializedCategory objD}
       (F G : SpecializedFunctor C D)
  := {
      ComponentsOf :> forall c, D.(Morphism) (F c) (G c)
    }.

Definition ProductCategory
           `(C : @SpecializedCategory objC)
           `(D : @SpecializedCategory objD)
: @SpecializedCategory (objC * objD)%type
  := @Build_SpecializedCategory _
                                (fun s d => (C.(Morphism) (fst s) (fst d) * D.(Morphism) (snd s) (snd d))%type)
                                (fun s d d' m2 m1 => (Compose (fst m2) (fst m1), Compose (snd m2) (snd m1))).

Infix "*" := ProductCategory : category_scope.

Section ProductCategoryFunctors.
  Context `{C : @SpecializedCategory objC}.
  Context `{D : @SpecializedCategory objD}.

  Definition fst_Functor : SpecializedFunctor (C * D) C
    := Build_SpecializedFunctor (C * D) C
                                (@fst _ _)
                                (fun _ _ => @fst _ _).

  Definition snd_Functor : SpecializedFunctor (C * D) D
    := Build_SpecializedFunctor (C * D) D
                                (@snd _ _)
                                (fun _ _ => @snd _ _).
End ProductCategoryFunctors.


Definition OppositeCategory `(C : @SpecializedCategory objC) : @SpecializedCategory objC :=
  @Build_SpecializedCategory objC
                             (fun s d => Morphism C d s)
                             (fun _ _ _ m1 m2 => Compose m2 m1).

Section OppositeFunctor.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Variable F : SpecializedFunctor C D.
  Let COp := OppositeCategory C.
  Let DOp := OppositeCategory D.

  Definition OppositeFunctor : SpecializedFunctor COp DOp
    := Build_SpecializedFunctor COp DOp
                                (fun c : COp => F c : DOp)
                                (fun (s d : COp) (m : C.(Morphism) d s) => MorphismOf F (s := d) (d := s) m).
End OppositeFunctor.

Section FunctorProduct.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Context `(D' : @SpecializedCategory objD').

  Definition FunctorProduct (F : Functor C D) (F' : Functor C D') : SpecializedFunctor C (D * D').
    match goal with
      | [ |- SpecializedFunctor ?C0 ?D0 ] =>
        refine (Build_SpecializedFunctor
                  C0 D0
                  (fun c => (F c, F' c))
                  (fun s d m => (MorphismOf F m, MorphismOf F' m)))
    end.
  Defined.
End FunctorProduct.

Section FunctorProduct'.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Context `(C' : @SpecializedCategory objC').
  Context `(D' : @SpecializedCategory objD').
  Variable F : Functor C D.
  Variable F' : Functor C' D'.

  Definition FunctorProduct' : SpecializedFunctor  (C * C') (D * D')
    := FunctorProduct (ComposeFunctors F fst_Functor) (ComposeFunctors F' snd_Functor).
End FunctorProduct'.

(** XXX TODO(jgross): Change this to [FunctorProduct]. *)
Infix "*" := FunctorProduct' : functor_scope.

Definition TypeCat : @SpecializedCategory Type :=
  (@Build_SpecializedCategory Type
                              (fun s d => s -> d)
                              (fun _ _ _ f g => (fun x => f (g x)))).

Section HomFunctor.
  Context `(C : @SpecializedCategory objC).
  Let COp := OppositeCategory C.

  Definition CovariantHomFunctor (A : COp) : SpecializedFunctor C TypeCat
    := Build_SpecializedFunctor C TypeCat
                                (fun X : C => C.(Morphism) A X : TypeCat)
                                (fun X Y f => (fun g : C.(Morphism) A X => Compose f g)).

  Definition hom_functor_object_of (c'c : COp * C) := C.(Morphism) (fst c'c) (snd c'c) : TypeCat.

  Definition hom_functor_morphism_of (s's : (COp * C)%type) (d'd : (COp * C)%type) (hf : (COp * C).(Morphism) s's d'd) :
    TypeCat.(Morphism) (hom_functor_object_of s's) (hom_functor_object_of d'd).
    unfold hom_functor_object_of in *.
    destruct s's as [ s' s ], d'd as [ d' d ].
    destruct hf as [ h f ].
    intro g.
    exact (Compose f (Compose g h)).
  Defined.

  Definition HomFunctor : SpecializedFunctor (COp * C) TypeCat
    := Build_SpecializedFunctor (COp * C) TypeCat
                                (fun c'c : COp * C => C.(Morphism) (fst c'c) (snd c'c) : TypeCat)
                                (fun X Y (hf : (COp * C).(Morphism) X Y) => hom_functor_morphism_of hf).
End HomFunctor.

Section FullFaithful.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Variable F : SpecializedFunctor C D.
  Let COp := OppositeCategory C.
  Let DOp := OppositeCategory D.
  Let FOp := OppositeFunctor F.

  Definition InducedHomNaturalTransformation :
    SpecializedNaturalTransformation (HomFunctor C) (ComposeFunctors (HomFunctor D) (FOp * F))
    := (Build_SpecializedNaturalTransformation (HomFunctor C) (ComposeFunctors (HomFunctor D) (FOp * F))
                                               (fun sd : (COp * C) =>
                                                  MorphismOf F (s := _) (d := _))).
End FullFaithful.

Definition FunctorCategory
           `(C : @SpecializedCategory objC)
           `(D : @SpecializedCategory objD)
: @SpecializedCategory (SpecializedFunctor C D).
  refine (@Build_SpecializedCategory _
                                     (SpecializedNaturalTransformation (C := C) (D := D))
                                     _);
  admit.
Defined.

Notation "C ^ D" := (FunctorCategory D C) : category_scope.

Section Yoneda.
  Context `(C : @SpecializedCategory objC).
  Let COp := OppositeCategory C.

  Section Yoneda.
    Let Yoneda_NT s d (f : COp.(Morphism) s d) : SpecializedNaturalTransformation (CovariantHomFunctor C s) (CovariantHomFunctor C d)
      := Build_SpecializedNaturalTransformation
           (CovariantHomFunctor C s)
           (CovariantHomFunctor C d)
           (fun c : C => (fun m : C.(Morphism) _ _ => Compose m f)).

    Definition Yoneda : SpecializedFunctor COp (TypeCat ^ C)
      := Build_SpecializedFunctor COp (TypeCat ^ C)
                                  (fun c : COp => CovariantHomFunctor C c : TypeCat ^ C)
                                  (fun s d (f : Morphism COp s d) => Yoneda_NT s d f).
  End Yoneda.
End Yoneda.

Section FullyFaithful.
  Context `(C : @SpecializedCategory objC).

  Set Printing Universes.
  Check InducedHomNaturalTransformation (Yoneda C).
  (* Error: Universe inconsistency (cannot enforce Top.865 = Top.851 because
Top.851 < Top.869 <= Top.864 <= Top.865). *)
End FullyFaithful.
