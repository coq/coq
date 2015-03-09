Require Import TestSuite.admit.
Module FirstComment.
  Set Implicit Arguments.
  Generalizable All Variables.
  Set Asymmetric Patterns.
  Set Universe Polymorphism.

  Reserved Notation "x # y" (at level 40, left associativity).
  Reserved Notation "x #m y" (at level 40, left associativity).

  Delimit Scope object_scope with object.
  Delimit Scope morphism_scope with morphism.
  Delimit Scope category_scope with category.

  Record Category (obj : Type) :=
    {
      Object :> _ := obj;
      Morphism : obj -> obj -> Type;

      Identity : forall x, Morphism x x;
      Compose : forall s d d', Morphism d d' -> Morphism s d -> Morphism s d'
    }.

  Bind Scope object_scope with Object.
  Bind Scope morphism_scope with Morphism.

  Arguments Object {obj%type} C%category / : rename.
  Arguments Morphism {obj%type} !C%category s d : rename. (* , simpl nomatch. *)
  Arguments Identity {obj%type} [!C%category] x%object : rename.
  Arguments Compose {obj%type} [!C%category s%object d%object d'%object] m1%morphism m2%morphism : rename.

  Bind Scope category_scope with Category.

  Record Functor
         `(C : @Category objC)
         `(D : @Category objD)
    := {
        ObjectOf :> objC -> objD;
        MorphismOf : forall s d, C.(Morphism) s d -> D.(Morphism) (ObjectOf s) (ObjectOf d)
      }.

  Record NaturalTransformation
         `(C : @Category objC)
         `(D : @Category objD)
         (F G : Functor C D)
    := {
        ComponentsOf :> forall c, D.(Morphism) (F c) (G c)
      }.

  Definition ProductCategory
             `(C : @Category objC)
             `(D : @Category objD)
  : @Category (objC * objD)%type.
    refine (@Build_Category _
                            (fun s d => (C.(Morphism) (fst s) (fst d) * D.(Morphism) (snd s) (snd d))%type)
                            (fun o => (Identity (fst o), Identity (snd o)))
                            (fun s d d' m2 m1 => (Compose (fst m2) (fst m1), Compose (snd m2) (snd m1)))).

  Defined.

  Infix "*" := ProductCategory : category_scope.

  Record IsomorphismOf `{C : @Category objC} {s d} (m : C.(Morphism) s d) :=
    {
      IsomorphismOf_Morphism :> C.(Morphism) s d := m;
      Inverse : C.(Morphism) d s
    }.

  Record NaturalIsomorphism
         `(C : @Category objC)
         `(D : @Category objD)
         (F G : Functor C D)
    := {
        NaturalIsomorphism_Transformation :> NaturalTransformation F G;
        NaturalIsomorphism_Isomorphism : forall x : objC, IsomorphismOf (NaturalIsomorphism_Transformation x)
      }.

  Section PreMonoidalCategory.
    Context `(C : @Category objC).

    Variable TensorProduct : Functor (C * C) C.

    Let src {C : @Category objC} {s d} (_ : Morphism C s d) := s.
    Let dst {C : @Category objC} {s d} (_ : Morphism C s d) := d.

    Local Notation "A # B" := (TensorProduct (A, B)).
    Local Notation "A #m B" := (TensorProduct.(MorphismOf) ((@src _ _ _ A, @src _ _ _ B)) ((@dst _ _ _ A, @dst _ _ _ B)) (A, B)%morphism).

    Let TriMonoidalProductL_ObjectOf (abc : C * C * C) : C :=
      (fst (fst abc) # snd (fst abc)) # snd abc.

    Let TriMonoidalProductR_ObjectOf (abc : C * C * C) : C :=
      fst (fst abc) # (snd (fst abc) # snd abc).

    Let TriMonoidalProductL_MorphismOf (s d : C * C * C) (m : Morphism (C * C * C) s d) :
      Morphism C (TriMonoidalProductL_ObjectOf s) (TriMonoidalProductL_ObjectOf d).
    Admitted.

    Let TriMonoidalProductR_MorphismOf (s d : C * C * C) (m : Morphism (C * C * C) s d) :
      Morphism C (TriMonoidalProductR_ObjectOf s) (TriMonoidalProductR_ObjectOf d).
    Admitted.

    Definition TriMonoidalProductL : Functor (C * C * C) C.
      refine (Build_Functor (C * C * C) C
                            TriMonoidalProductL_ObjectOf
                            TriMonoidalProductL_MorphismOf).
    Defined.

    Definition TriMonoidalProductR : Functor (C * C * C) C.
      refine (Build_Functor (C * C * C) C
                            TriMonoidalProductR_ObjectOf
                            TriMonoidalProductR_MorphismOf).
    Defined.

    Variable Associator : NaturalIsomorphism TriMonoidalProductL TriMonoidalProductR.

    Section AssociatorCoherenceCondition.
      Variables a b c d : C.

      (* going from top-left *)
      Let AssociatorCoherenceConditionT0 : Morphism C (((a # b) # c) # d) ((a # (b # c)) # d)
        := Associator (a, b, c) #m Identity (C := C) d.
      Let AssociatorCoherenceConditionT1 : Morphism C ((a # (b # c)) # d) (a # ((b # c) # d))
        := Associator (a, b # c, d).
      Let AssociatorCoherenceConditionT2 : Morphism C (a # ((b # c) # d)) (a # (b # (c # d)))
        := Identity (C := C) a #m Associator (b, c, d).
      Let AssociatorCoherenceConditionB0 : Morphism C (((a # b) # c) # d) ((a # b) # (c # d))
        := Associator (a # b, c, d).
      Let AssociatorCoherenceConditionB1 : Morphism C ((a # b) # (c # d)) (a # (b # (c # d)))
        := Associator (a, b, c # d).

      Definition AssociatorCoherenceCondition' :=
        Compose AssociatorCoherenceConditionT2 (Compose AssociatorCoherenceConditionT1 AssociatorCoherenceConditionT0)
        = Compose AssociatorCoherenceConditionB1 AssociatorCoherenceConditionB0.
    End AssociatorCoherenceCondition.

    Definition AssociatorCoherenceCondition := Eval unfold AssociatorCoherenceCondition' in
                                                forall a b c d : C, AssociatorCoherenceCondition' a b c d.
  End PreMonoidalCategory.

  Section MonoidalCategory.
    Variable objC : Type.

    Let AssociatorCoherenceCondition' := Eval unfold AssociatorCoherenceCondition in @AssociatorCoherenceCondition.

    Record MonoidalCategory :=
      {
        MonoidalUnderlyingCategory :> @Category objC;
        TensorProduct : Functor (MonoidalUnderlyingCategory * MonoidalUnderlyingCategory) MonoidalUnderlyingCategory;
        IdentityObject : objC;
        Associator : NaturalIsomorphism (TriMonoidalProductL TensorProduct) (TriMonoidalProductR TensorProduct);
        AssociatorCoherent : AssociatorCoherenceCondition' Associator
      }.
  End MonoidalCategory.

  Section EnrichedCategory.
    Context `(M : @MonoidalCategory objM).
    Let x : M := IdentityObject M.
    (* Anomaly: apply_coercion_args: mismatch between arguments and coercion. Please report.  *)
  End EnrichedCategory.
End FirstComment.

Module SecondComment.
  Set Implicit Arguments.
  Set Universe Polymorphism.
  Generalizable All Variables.

  Record prod (A B : Type) := pair { fst : A; snd : B }.
  Arguments fst {A B} _.
  Arguments snd {A B} _.
  Infix "*" := prod : type_scope.
  Notation " ( x , y ) " := (@pair _ _ x y).
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

  Arguments MorphismOf {objC%type} [C] {objD%type} [D] F [s d] m : rename, simpl nomatch.

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
      refine {| ObjectOf := (fun x => x);
                MorphismOf := (fun _ _ x => x)
             |}.
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

  Definition OppositeCategory `(C : @Category objC) : Category objC :=
    @Build_Category objC
                    (fun s d => Morphism C d s)
                    (Identity (C := C))
                    (fun _ _ _ m1 m2 => Compose m2 m1).

  Parameter FunctorCategory : forall `(C : @Category objC) `(D : @Category objD), @Category (Functor C D).

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

  Section SmallCat.
    Definition LocallySmallCat := ComputableCategory _ LSUnderlyingCategory.
  End SmallCat.

  Section CommaCategory.
    Context `(A : @Category objA).
    Context `(B : @Category objB).
    Context `(C : @Category objC).
    Variable S : Functor A C.
    Variable T : Functor B C.

    Record CommaCategory_Object := { CommaCategory_Object_Member :> { ab : objA * objB & C.(Morphism) (S (fst ab)) (T (snd ab)) } }.

    Let SortPolymorphic_Helper (A T : Type) (Build_T : A -> T) := A.

    Definition CommaCategory_ObjectT := Eval hnf in SortPolymorphic_Helper Build_CommaCategory_Object.
    Definition Build_CommaCategory_Object' (mem : CommaCategory_ObjectT) := Build_CommaCategory_Object mem.
    Global Coercion Build_CommaCategory_Object' : CommaCategory_ObjectT >-> CommaCategory_Object.

    Definition CommaCategory : @Category CommaCategory_Object.
    Admitted.
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
    Context `(C : Category objC).

    Variable S : (OppositeCategory (FunctorCategory A C)).
    Variable T : (FunctorCategory B C).

    Definition CommaCategoryProjection : Functor (CommaCategory S T) (ProductCategory A B).
    Admitted.

    Definition CommaCategoryProjectionFunctor_ObjectOf
    : @SliceCategoryOver _ LocallySmallCat (ProductCategory A B)
      :=
        existT _
               ((CommaCategory S T) : Category', tt)
               (CommaCategoryProjection) :
          CommaCategory_ObjectT (IdentityFunctor _)
                                (SliceCategory_Functor LocallySmallCat
                                                       (ProductCategory A B)).
    (* Anomaly: apply_coercion_args: mismatch between arguments and coercion. Please report. *)
    (* Toplevel input, characters 110-142:
Error:
In environment
objA : Type
A : Category objA
objB : Type
B : Category objB
objC : Type
C : Category objC
S : OppositeCategory (FunctorCategory A C)
T : FunctorCategory B C
The term "ProductCategory A B:Category (objA * objB)" has type
 "Category (objA * objB)" while it is expected to have type
 "Object LocallySmallCat".
 *)
  End CommaCategoryProjectionFunctor.
End SecondComment.
