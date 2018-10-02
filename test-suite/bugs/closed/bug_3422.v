Require Import TestSuite.admit.
Generalizable All Variables.
Set Implicit Arguments.
Set Universe Polymorphism.
Axiom admit : forall {T}, T.
Reserved Infix "o" (at level 40, left associativity).
Class IsEquiv {A B : Type} (f : A -> B) := { equiv_inv : B -> A }.
Record Equiv A B := { equiv_fun :> A -> B ; equiv_isequiv :> IsEquiv equiv_fun }.
Existing Instance equiv_isequiv.
Delimit Scope equiv_scope with equiv.
Local Open Scope equiv_scope.
Notation "A <~> B" := (Equiv A B) (at level 85) : equiv_scope.
Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3) : equiv_scope.
Axiom IsHSet : Type -> Type.
Existing Class IsHSet.
Definition trunc_equiv' `(f : A <~> B) `{IsHSet A} : IsHSet B := admit.
Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Delimit Scope object_scope with object.
Record PreCategory :=
  { object :> Type;
    morphism : object -> object -> Type;

    compose : forall s d d',
                morphism d d'
                -> morphism s d
                -> morphism s d'
                            where "f 'o' g" := (compose f g);

    trunc_morphism : forall s d, IsHSet (morphism s d) }.

Bind Scope category_scope with PreCategory.
Infix "o" := (@compose _ _ _ _) : morphism_scope.

Delimit Scope functor_scope with functor.

Record Functor (C D : PreCategory) :=
  {
    object_of :> C -> D;
    morphism_of : forall s d, morphism C s d
                              -> morphism D (object_of s) (object_of d)
  }.

Bind Scope functor_scope with Functor.
Arguments morphism_of [C%category] [D%category] F%functor [s%object d%object] m%morphism : rename, simpl nomatch.
Notation "F '_1' m" := (morphism_of F m) (at level 10, no associativity) : morphism_scope.
Local Open Scope morphism_scope.

Class IsIsomorphism {C : PreCategory} {s d} (m : morphism C s d) := { morphism_inverse : morphism C d s }.

Local Notation "m ^-1" := (morphism_inverse (m := m)) : morphism_scope.

Class Isomorphic {C : PreCategory} s d :=
  {
    morphism_isomorphic :> morphism C s d;
    isisomorphism_isomorphic :> IsIsomorphism morphism_isomorphic
  }.

Coercion morphism_isomorphic : Isomorphic >-> morphism.

Local Infix "<~=~>" := Isomorphic (at level 70, no associativity) : category_scope.

Definition isisomorphism_inverse `(@IsIsomorphism C x y m) : IsIsomorphism m^-1 := {| morphism_inverse := m |}.

Global Instance isisomorphism_compose `(@IsIsomorphism C y z m0) `(@IsIsomorphism C x y m1)
: IsIsomorphism (m0 o m1).
admit.
Defined.

Section composition.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.
  Variable G : Functor D E.
  Variable F : Functor C D.

  Definition composeF : Functor C E
    := Build_Functor
         C E
         (fun c => G (F c))
         (fun _ _ m => morphism_of G (morphism_of F m)).
End composition.
Infix "o" := composeF : functor_scope.

Delimit Scope natural_transformation_scope with natural_transformation.
Record NaturalTransformation C D (F G : Functor C D) := { components_of :> forall c, morphism D (F c) (G c) }.

Section compose.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variables F F' F'' : Functor C D.

  Variable T' : NaturalTransformation F' F''.
  Variable T : NaturalTransformation F F'.

  Local Notation CO c := (T' c o T c).

  Definition composeT
  : NaturalTransformation F F'' := Build_NaturalTransformation F F'' (fun c => CO c).

End compose.

Section whisker.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variable E : PreCategory.

  Section L.
    Variable F : Functor D E.
    Variables G G' : Functor C D.
    Variable T : NaturalTransformation G G'.

    Local Notation CO c := (morphism_of F (T c)).

    Definition whisker_l
      := Build_NaturalTransformation
           (F o G) (F o G')
           (fun c => CO c).

  End L.

  Section R.
    Variables F F' : Functor D E.
    Variable T : NaturalTransformation F F'.
    Variable G : Functor C D.

    Local Notation CO c := (T (G c)).

    Definition whisker_r
      := Build_NaturalTransformation
           (F o G) (F' o G)
           (fun c => CO c).
  End R.
End whisker.
Infix "o" := composeT : natural_transformation_scope.
Infix "oL" := whisker_l (at level 40, left associativity) : natural_transformation_scope.
Infix "oR" := whisker_r (at level 40, left associativity) : natural_transformation_scope.

Section path_natural_transformation.

  Variable C : PreCategory.
  Variable D : PreCategory.
  Variables F G : Functor C D.

  Lemma equiv_sig_natural_transformation
  : { CO : forall x, morphism D (F x) (G x)
    | forall s d (m : morphism C s d),
        CO d o F _1 m = G _1 m o CO s }
      <~> NaturalTransformation F G.
    admit.
  Defined.

  Global Instance trunc_natural_transformation
  : IsHSet (NaturalTransformation F G).
  Proof.
    eapply trunc_equiv'; [ exact equiv_sig_natural_transformation | ].
    admit.
  Qed.

End path_natural_transformation.
Definition functor_category (C D : PreCategory) : PreCategory
  := @Build_PreCategory (Functor C D) (@NaturalTransformation C D) (@composeT C D) _.

Notation "C -> D" := (functor_category C D) : category_scope.

Definition NaturalIsomorphism (C D : PreCategory) F G := @Isomorphic (C -> D) F G.

Coercion natural_transformation_of_natural_isomorphism C D F G (T : @NaturalIsomorphism C D F G) : NaturalTransformation F G
  := T : morphism _ _ _.
Local Infix "<~=~>" := NaturalIsomorphism : natural_transformation_scope.
Global Instance isisomorphism_compose'
       `(T' : @NaturalTransformation C D F' F'')
       `(T : @NaturalTransformation C D F F')
       `{@IsIsomorphism (C -> D) F' F'' T'}
       `{@IsIsomorphism (C -> D) F F' T}
: @IsIsomorphism (C -> D) F F'' (T' o T)%natural_transformation
  := @isisomorphism_compose (C -> D) _ _ T' _ _ T _.

Section lemmas.
  Local Open Scope natural_transformation_scope.

  Variable C : PreCategory.
  Variable F : C -> PreCategory.
  Context
    {w x y z}
    {f : Functor (F w) (F z)} {f0 : Functor (F w) (F y)}
    {f1 : Functor (F x) (F y)} {f2 : Functor (F y) (F z)}
    {f3 : Functor (F w) (F x)} {f4 : Functor (F x) (F z)}
    {f5 : Functor (F w) (F z)} {n : f5 <~=~> (f4 o f3)%functor}
    {n0 : f4 <~=~> (f2 o f1)%functor} {n1 : f0 <~=~> (f1 o f3)%functor}
    {n2 : f <~=~> (f2 o f0)%functor}.

  Lemma p_composition_of_coherent_iso_for_rewrite__isisomorphism_helper'
  : @IsIsomorphism
      (_ -> _) _ _
      (n2 ^-1 o (f2 oL n1 ^-1 o (admit o (n0 oR f3 o n))))%natural_transformation.
  Proof.
    eapply isisomorphism_compose';
    [ eapply isisomorphism_inverse
    | eapply isisomorphism_compose';
      [ admit
      | eapply isisomorphism_compose';
        [ admit |
          eapply isisomorphism_compose'; [ admit | ]]]].
    Set Printing All. Set Printing Universes.
    apply @isisomorphism_isomorphic.
  Qed.

End lemmas.
