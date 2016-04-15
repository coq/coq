Require Import TestSuite.admit.
Set Universe Polymorphism.
Class Funext := { }.
Delimit Scope category_scope with category.
Record PreCategory := { object :> Type ; morphism : object -> object -> Type }.
Set Implicit Arguments.
Record Functor (C D : PreCategory) :=
  { object_of :> C -> D;
    morphism_of : forall s d, morphism C s d -> morphism D (object_of s) (object_of d);
    identity_of : forall s m, morphism_of s s m = morphism_of s s m }.
Definition sub_pre_cat `{Funext} (P : PreCategory -> Type) : PreCategory.
Proof.
  exact (@Build_PreCategory PreCategory Functor).
Defined.
Definition opposite (C : PreCategory) : PreCategory.
Proof.
  exact (@Build_PreCategory C (fun s d => morphism C d s)).
Defined.
Local Notation "C ^op" := (opposite C) (at level 3, format "C '^op'") : category_scope.
Definition prod (C D : PreCategory) : PreCategory.
Proof.
  refine (@Build_PreCategory
            (C * D)%type
            (fun s d => (morphism C (fst s) (fst d) * morphism D (snd s) (snd d))%type)).
Defined.
Local Infix "*" := prod : category_scope.
Record NaturalTransformation C D (F G : Functor C D) := {}.
Definition functor_category (C D : PreCategory) : PreCategory.
Proof.
  exact (@Build_PreCategory (Functor C D) (@NaturalTransformation C D)).
Defined.
Local Notation "C -> D" := (functor_category C D) : category_scope.
Module Export PointwiseCore.
  Local Open Scope category_scope.
  Definition pointwise
             (C C' : PreCategory)
             (F : Functor C' C)
             (D D' : PreCategory)
             (G : Functor D D')
  : Functor (C -> D) (C' -> D').
  Proof.
    unshelve (refine (Build_Functor
              (C -> D) (C' -> D')
              _
              _
              _));
    abstract admit.
  Defined.
End PointwiseCore.
Axiom Pidentity_of : forall (C D : PreCategory) (F : Functor C C) (G : Functor D D), pointwise F G = pointwise F G.
Local Open Scope category_scope.
Module Success.
  Definition functor_uncurried `{Funext} (P : PreCategory -> Type)
             (has_functor_categories : forall C D : sub_pre_cat P, P (C -> D))
  : object (((sub_pre_cat P)^op * (sub_pre_cat P)) -> (sub_pre_cat P))
    := Eval cbv zeta in
        let object_of := (fun CD => (((fst CD) -> (snd CD))))
        in Build_Functor
             ((sub_pre_cat P)^op * (sub_pre_cat P)) (sub_pre_cat P)
             object_of
             (fun CD C'D' FG => pointwise (fst FG) (snd FG))
             (fun _ _ => @Pidentity_of _ _ _ _).
End Success.
Module Bad.
  Include PointwiseCore.
  Definition functor_uncurried `{Funext} (P : PreCategory -> Type)
             (has_functor_categories : forall C D : sub_pre_cat P, P (C -> D))
  : object (((sub_pre_cat P)^op * (sub_pre_cat P)) -> (sub_pre_cat P))
    := Eval cbv zeta in
        let object_of := (fun CD => (((fst CD) -> (snd CD))))
        in Build_Functor
             ((sub_pre_cat P)^op * (sub_pre_cat P)) (sub_pre_cat P)
             object_of
             (fun CD C'D' FG => pointwise (fst FG) (snd FG))
             (fun _ _ => @Pidentity_of _ _ _ _).
