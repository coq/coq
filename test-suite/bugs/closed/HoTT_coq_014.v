Require Import TestSuite.admit.
Set Implicit Arguments.
Generalizable All Variables.
Set Universe Polymorphism.

Polymorphic Record SpecializedCategory@{l k} (obj : Type@{l}) := Build_SpecializedCategory' {
  Object :> Type@{l} := obj;
  Morphism' : obj -> obj -> Type@{k};

  Identity' : forall o, Morphism' o o;
  Compose' : forall s d d', Morphism' d d' -> Morphism' s d -> Morphism' s d'
}.

Polymorphic Definition Morphism obj (C : @SpecializedCategory obj) : forall s d : C, _ := Eval cbv beta delta [Morphism'] in C.(Morphism').

(* eh, I'm not terribly happy.  meh. *)
Polymorphic Definition SmallSpecializedCategory (obj : Set) (*mor : obj -> obj -> Set*) := SpecializedCategory@{Set Set} obj.
Polymorphic Identity Coercion SmallSpecializedCategory_LocallySmallSpecializedCategory_Id : SmallSpecializedCategory >-> SpecializedCategory.

Polymorphic Record Category := {
  CObject : Type;

  UnderlyingCategory :> @SpecializedCategory CObject
}.

Polymorphic Definition GeneralizeCategory `(C : @SpecializedCategory obj) : Category.
  refine {| CObject := C.(Object) |}; auto.
Defined.

Polymorphic Coercion GeneralizeCategory : SpecializedCategory >-> Category.



Section SpecializedFunctor.
  Set Universe Polymorphism.
  Context `(C : @SpecializedCategory objC).
  Context `(D : @SpecializedCategory objD).
  Unset Universe Polymorphism.

  Polymorphic Record SpecializedFunctor := {
    ObjectOf' : objC -> objD;
    MorphismOf' : forall s d, C.(Morphism') s d -> D.(Morphism') (ObjectOf' s) (ObjectOf' d);
    FCompositionOf' : forall s d d' (m1 : C.(Morphism') s d) (m2: C.(Morphism') d d'),
      MorphismOf' _ _ (C.(Compose') _ _ _ m2 m1) = D.(Compose') _ _ _ (MorphismOf' _ _ m2) (MorphismOf' _ _ m1);
    FIdentityOf' : forall o, MorphismOf' _ _ (C.(Identity') o) = D.(Identity') (ObjectOf' o)
  }.
End SpecializedFunctor.

Global Polymorphic Coercion ObjectOf' : SpecializedFunctor >-> Funclass.
Set Universe Polymorphism.
Section Functor.
  Variable C D : Category.

  Polymorphic Definition Functor := SpecializedFunctor C D.
End Functor.
Unset Universe Polymorphism.

Polymorphic Identity Coercion Functor_SpecializedFunctor_Id : Functor >-> SpecializedFunctor.
Polymorphic Definition GeneralizeFunctor objC C objD D (F : @SpecializedFunctor objC C objD D) : Functor C D := F.
Polymorphic Coercion GeneralizeFunctor : SpecializedFunctor >-> Functor.

Arguments SpecializedFunctor {objC} C {objD} D.


Polymorphic Record SmallCategory := {
  SObject : Set;

  SUnderlyingCategory :> @SmallSpecializedCategory SObject
}.

Polymorphic Definition GeneralizeSmallCategory `(C : @SmallSpecializedCategory obj) : SmallCategory.
  refine {| SObject := obj |}; destruct C; econstructor; eassumption.
Defined.

Polymorphic Coercion GeneralizeSmallCategory : SmallSpecializedCategory >-> SmallCategory.

Bind Scope category_scope with SmallCategory.


Polymorphic Definition TypeCat : @SpecializedCategory Type := (@Build_SpecializedCategory' Type
                                                                                          (fun s d => s -> d)
                                                                                          (fun _ => (fun x => x))
                                                                                          (fun _ _ _ f g => (fun x => f (g x)))).
(*Unset Universe Polymorphism.*)
Polymorphic Definition FunctorCategory objC (C : @SpecializedCategory objC) objD (D : @SpecializedCategory objD) :
  @SpecializedCategory (SpecializedFunctor C D).
Admitted.

Polymorphic Definition DiscreteCategory (O : Type) : @SpecializedCategory O.
Admitted.

Polymorphic Definition ComputableCategory (I : Type) (Index2Object : I -> Type) (Index2Cat : forall i : I, @SpecializedCategory (@Index2Object i)) :
  @SpecializedCategory I.
Admitted.

Polymorphic Definition is_unique (A : Type) (x : A) := forall x' : A, x' = x.

Polymorphic Definition InitialObject obj {C : SpecializedCategory obj} (o : C) :=
    forall o', { m : C.(Morphism) o o' | is_unique m }.

Polymorphic Definition SmallCat := ComputableCategory _ SUnderlyingCategory.

Lemma InitialCategory_Initial : InitialObject (C := SmallCat) (DiscreteCategory Empty_set : SmallSpecializedCategory _).
  admit.
Qed.

Set Universe Polymorphism.
Section GraphObj.
  Context `(C : @SpecializedCategory objC).

  Inductive GraphIndex := GraphIndexSource | GraphIndexTarget.

  Definition GraphIndex_Morphism (a b : GraphIndex) : Set :=
    match (a, b) with
      | (GraphIndexSource, GraphIndexSource) => unit
      | (GraphIndexTarget, GraphIndexTarget) => unit
      | (GraphIndexTarget, GraphIndexSource) => Empty_set
      | (GraphIndexSource, GraphIndexTarget) => GraphIndex
    end.

  Global Arguments GraphIndex_Morphism a b /.

  Definition GraphIndex_Compose s d d' (m1 : GraphIndex_Morphism d d') (m2 : GraphIndex_Morphism s d) :
    GraphIndex_Morphism s d'.
  Proof using.  (* This makes no sense, but it makes this test behave as before the no admit commit *)
  Admitted.

   Definition GraphIndexingCategory : @SpecializedCategory GraphIndex.
    refine {|
      Morphism' := GraphIndex_Morphism;
      Identity' := (fun x => match x with GraphIndexSource => tt | GraphIndexTarget => tt end);
      Compose' := GraphIndex_Compose
    |};
    admit.
  Defined.

  Definition UnderlyingGraph_ObjectOf x :=
    match x with
      | GraphIndexSource => { sd : objC * objC & C.(Morphism) (fst sd) (snd sd) }
      | GraphIndexTarget => objC
    end.

  Global Arguments UnderlyingGraph_ObjectOf x /.

  Definition UnderlyingGraph_MorphismOf s d (m : Morphism GraphIndexingCategory s d) :
    UnderlyingGraph_ObjectOf s -> UnderlyingGraph_ObjectOf d.
  Admitted.

  Definition UnderlyingGraph : SpecializedFunctor GraphIndexingCategory TypeCat.
  Proof.
    match goal with
      | [ |- SpecializedFunctor ?C ?D ] =>
        refine (Build_SpecializedFunctor C D
          UnderlyingGraph_ObjectOf
          UnderlyingGraph_MorphismOf
          _
          _
        )
    end;
    admit.
  Defined.
End GraphObj.

Set Printing Universes.
Set Printing All.

Print Coercions.

Section test.

Fail Polymorphic Definition UnderlyingGraphFunctor_MorphismOf' (C D : SmallCategory) (F : SpecializedFunctor C D) :
    Morphism (FunctorCategory TypeCat GraphIndexingCategory)
    (@UnderlyingGraph (SObject C)
                     (SmallSpecializedCategory_LocallySmallSpecializedCategory_Id (SUnderlyingCategory C)))
    (UnderlyingGraph D).
 (* Toplevel input, characters 216-249:
Error:
In environment
C : SmallCategory (* Top.594 *)
D : SmallCategory (* Top.595 *)
F :
@SpecializedFunctor (* Top.25 Set Top.25 Set *) (SObject (* Top.25 *) C)
  (SUnderlyingCategory (* Top.25 *) C) (SObject (* Top.25 *) D)
  (SUnderlyingCategory (* Top.25 *) D)
The term
 "SUnderlyingCategory (* Top.25 *) C
  :SpecializedCategory (* Top.25 Set *) (SObject (* Top.25 *) C)" has type
 "SpecializedCategory (* Top.618 Top.619 *) (SObject (* Top.25 *) C)"
while it is expected to have type
 "SpecializedCategory (* Top.224 Top.225 *) (SObject (* Top.617 *) C)"
(Universe inconsistency: Cannot enforce Set = Top.225)).
 *)
Fail Admitted.

Fail Polymorphic Definition UnderlyingGraphFunctor_MorphismOf (C D : SmallCategory) (F : SpecializedFunctor C D) :
  Morphism (FunctorCategory TypeCat GraphIndexingCategory) (UnderlyingGraph C) (UnderlyingGraph D). (* Anomaly: apply_coercion. Please report.*)
Fail Admitted.

Polymorphic Definition UnderlyingGraphFunctor_MorphismOf (C D : SmallCategory) (F : SpecializedFunctor C D) :
  Morphism (FunctorCategory GraphIndexingCategory TypeCat) (UnderlyingGraph C) (UnderlyingGraph D). (* Anomaly: apply_coercion. Please report.*)
Proof.
Admitted.
