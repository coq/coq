Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from 335 lines to 115 lines. *)
Set Implicit Arguments.
Set Universe Polymorphism.
Generalizable All Variables.
Record Category (obj : Type) :=
  Build_Category {
      Object :> _ := obj;
      Morphism : obj -> obj -> Type;

      Identity : forall x, Morphism x x;
      Compose : forall s d d', Morphism d d' -> Morphism s d -> Morphism s d'
    }.

Arguments Identity {obj%type} [!C] x : rename.

Arguments Compose {obj%type} [!C s d d'] m1 m2 : rename.
Record > Category' :=
  {
    LSObject : Type;

    LSUnderlyingCategory :> @Category LSObject
  }.

Section Functor.

  Context `(C : @Category objC).
  Context `(D : @Category objD).
  Record Functor :=
    {
      ObjectOf :> objC -> objD;
      MorphismOf : forall s d, C.(Morphism) s d -> D.(Morphism) (ObjectOf s) (ObjectOf d)
    }.

End Functor.
Section FunctorComposition.

  Context `(C : @Category objC).
  Context `(D : @Category objD).
  Context `(E : @Category objE).
  Definition ComposeFunctors (G : Functor D E) (F : Functor C D) : Functor C E.

  Admitted.
End FunctorComposition.
Section IdentityFunctor.

  Context `(C : @Category objC).
  Definition IdentityFunctor : Functor C C.

    admit.
  Defined.
End IdentityFunctor.
Section ProductCategory.

  Context `(C : @Category objC).
  Context `(D : @Category objD).
  Definition ProductCategory : @Category (objC * objD)%type.

    refine (@Build_Category _
                            (fun s d => (C.(Morphism) (fst s) (fst d) * D.(Morphism) (snd s) (snd d))%type)
                            (fun o => (Identity (fst o), Identity (snd o)))
                            (fun s d d' m2 m1 => (Compose (fst m2) (fst m1), Compose (snd m2) (snd m1)))).
  Defined.
End ProductCategory.
Parameter TerminalCategory : Category unit.

Section ComputableCategory.

  Variable I : Type.
  Variable Index2Object : I -> Type.
  Variable Index2Cat : forall i : I, @Category (@Index2Object i).
  Local Coercion Index2Cat : I >-> Category.

  Definition ComputableCategory : @Category I.

    refine (@Build_Category _
                            (fun C D : I => Functor C D)
                            (fun o : I => IdentityFunctor o)
                            (fun C D E : I => ComposeFunctors (C := C) (D := D) (E := E))).
  Defined.
End ComputableCategory.
Definition LocallySmallCat := ComputableCategory _ LSUnderlyingCategory.
Section CommaCategory.

  Context `(A : @Category objA).
  Context `(B : @Category objB).
  Context `(C : @Category objC).
  Variable S : Functor A C.
  Variable T : Functor B C.
  Record CommaCategory_Object := { CommaCategory_Object_Member :> { ab : objA * objB & C.(Morphism) (S (fst ab)) (T (snd ab)) } }.

End CommaCategory.
Definition SliceCategory_Functor `(C : @Category objC) (a : C) : Functor TerminalCategory C
  := {| ObjectOf := (fun _ => a);
        MorphismOf := (fun _ _ _ => Identity a)
     |}.

Definition SliceCategoryOver
: forall (objC : Type) (C : Category objC) (a : C),
    Category
      (CommaCategory_Object (IdentityFunctor C)
                            (SliceCategory_Functor C a)).

  admit.
Defined.
Section CommaCategoryProjectionFunctor.

  Context `(A : Category objA).
  Context `(B : Category objB).
  Let X : LocallySmallCat.

  Proof.
    hnf.
    pose (@SliceCategoryOver _ LocallySmallCat).
    exact (ProductCategory A B).
    Set Printing Universes.
  Defined.
(* Error: Illegal application:
The term
 "CommaCategory_Object (* Top.306 Top.307 Top.305 Top.300 Top.305 Top.306 *)"
of type
 "forall (objA : Type (* Top.305 *))
    (A : Category (* Top.306 Top.305 *) objA) (objB : Type (* Top.307 *))
    (B : Category (* Top.300 Top.307 *) objB) (objC : Type (* Top.305 *))
    (C : Category (* Top.306 Top.305 *) objC),
  Functor (* Top.306 Top.305 Top.305 Top.306 *) A C ->
  Functor (* Top.300 Top.307 Top.305 Top.306 *) B C ->
  Type (* max(Top.307, Top.305, Top.306) *)"
cannot be applied to the terms
 "Category' (* Top.312 Top.311 *)" : "Type (* max(Top.311+1, Top.312+1) *)"
 "LocallySmallCat (* Top.309 Top.310 Top.311 Top.312 Top.313 Top.314 Top.306 Top.316 Top.305 *)"
   : "Category (* Top.306 Top.305 *) Category' (* Top.312 Top.311 *)"
 "unit" : "Set"
 "TerminalCategory (* Top.300 *)" : "Category (* Top.300 Set *) unit"
 "Category' (* Top.312 Top.311 *)" : "Type (* max(Top.311+1, Top.312+1) *)"
 "LocallySmallCat (* Top.309 Top.310 Top.311 Top.312 Top.313 Top.314 Top.306 Top.316 Top.305 *)"
   : "Category (* Top.306 Top.305 *) Category' (* Top.312 Top.311 *)"
 "IdentityFunctor (* Top.299 Top.302 Top.301 Top.305 Top.306 *)
    LocallySmallCat (* Top.309 Top.310 Top.311 Top.312 Top.313 Top.314
    Top.306 Top.316 Top.305 *)"
   : "Functor (* Top.306 Top.305 Top.305 Top.306 *) LocallySmallCat
        (* Top.309 Top.310 Top.311 Top.312 Top.313 Top.314 Top.306 Top.316
        Top.305 *) LocallySmallCat (* Top.309 Top.310 Top.311 Top.312 Top.313
        Top.314 Top.306 Top.316 Top.305 *)"
 "SliceCategory_Functor (* Top.305 Top.306 Top.307 Top.300 *) LocallySmallCat
    (* Top.309 Top.310 Top.311 Top.312 Top.313 Top.314 Top.306 Top.316
    Top.305 *) a"
   : "Functor (* Top.300 Top.307 Top.305 Top.306 *) TerminalCategory
        (* Top.300 *) LocallySmallCat (* Top.309 Top.310 Top.311 Top.312
        Top.313 Top.314 Top.306 Top.316 Top.305 *)"
The 4th term has type "Category (* Top.300 Set *) unit"
which should be coercible to "Category (* Top.300 Top.307 *) unit". *)
