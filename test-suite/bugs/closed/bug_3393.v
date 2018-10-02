Require Import TestSuite.admit.
(* -*- coq-prog-args: ("-indices-matter") -*- *)
(* File reduced by coq-bug-finder from original input, then from 8760 lines to 7519 lines, then from 7050 lines to 909 lines, then from 846 lines to 578 lines, then from 497 lines to 392 lines, then from 365 lines to 322 lines, then from 252 lines to 205 lines, then from 215 lines to 204 lines, then from 210 lines to 182 lines, then from 175 lines to 157 lines *)
Set Universe Polymorphism.
Axiom admit : forall {T}, T.
Set Implicit Arguments.
Generalizable All Variables.
Reserved Notation "g 'o' f" (at level 40, left associativity).
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a where "a = b" := (@paths _ a b) : type_scope.
Arguments idpath {A a} , [A] a.
Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g) : forall x, f x = g x := fun x => match h with idpath => idpath end.
Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv { equiv_inv : B -> A }.
Delimit Scope equiv_scope with equiv.
Local Open Scope equiv_scope.
Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3) : equiv_scope.
Class Funext := { isequiv_apD10 :> forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g) }.
Definition path_forall `{Funext} {A : Type} {P : A -> Type} (f g : forall x : A, P x) : (forall x, f x = g x) -> f = g := (@apD10 A P f g)^-1.
Record PreCategory :=
  { object :> Type;
    morphism : object -> object -> Type;
    compose : forall s d d', morphism d d' -> morphism s d -> morphism s d' where "f 'o' g" := (compose f g);
    associativity : forall x1 x2 x3 x4 (m1 : morphism x1 x2) (m2 : morphism x2 x3) (m3 : morphism x3 x4), (m3 o m2) o m1 = m3 o (m2 o m1)
  }.
Bind Scope category_scope with PreCategory.
Bind Scope morphism_scope with morphism.
Infix "o" := (@compose _ _ _ _) : morphism_scope.
Delimit Scope functor_scope with functor.
Record Functor (C D : PreCategory) :=
  { object_of :> C -> D;
    morphism_of : forall s d, morphism C s d -> morphism D (object_of s) (object_of d) }.
Bind Scope functor_scope with Functor.
Notation "F '_1' m" := (@morphism_of _ _ F _ _ m) (at level 10, no associativity) : morphism_scope.
Class IsIsomorphism {C : PreCategory} {s d} (m : morphism C s d) := { morphism_inverse : morphism C d s }.
Local Notation "m ^-1" := (morphism_inverse (m := m)) : morphism_scope.
Class Isomorphic {C : PreCategory} s d :=
  { morphism_isomorphic :> morphism C s d;
    isisomorphism_isomorphic :> IsIsomorphism morphism_isomorphic }.
Coercion morphism_isomorphic : Isomorphic >-> morphism.
Definition isisomorphism_inverse `(@IsIsomorphism C x y m) : IsIsomorphism m^-1 := {| morphism_inverse := m |}.

Global Instance isisomorphism_compose `(@IsIsomorphism C y z m0) `(@IsIsomorphism C x y m1) : IsIsomorphism (m0 o m1).
Admitted.
Infix "<~=~>" := Isomorphic (at level 70, no associativity) : category_scope.
Definition composef C D E (G : Functor D E) (F : Functor C D) : Functor C E
  := Build_Functor
       C E
       (fun c => G (F c))
       (fun _ _ m => @morphism_of _ _ G _ _ (@morphism_of _ _ F _ _ m)).
Infix "o" := composef : functor_scope.
Delimit Scope natural_transformation_scope with natural_transformation.

Local Open Scope morphism_scope.
Record NaturalTransformation C D (F G : Functor C D) :=
  { components_of :> forall c, morphism D (F c) (G c);
    commutes : forall s d (m : morphism C s d), components_of d o F _1 m = G _1 m o components_of s }.

Definition composet C D (F F' F'' : Functor C D) (T' : NaturalTransformation F' F'') (T : NaturalTransformation F F')
: NaturalTransformation F F''
  := Build_NaturalTransformation F F'' (fun c => T' c o T c) admit.
Infix "o" := composet : natural_transformation_scope.
Section path_natural_transformation.
  Context `{Funext}.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variables F G : Functor C D.
  Section path.
    Variables T U : NaturalTransformation F G.
    Lemma path'_natural_transformation
    : components_of T = components_of U
      -> T = U.
      admit.
    Defined.
    Lemma path_natural_transformation
    : (forall x, components_of T x = components_of U x)
      -> T = U.
    Proof.
      intros.
      apply path'_natural_transformation.
      apply path_forall; assumption.
    Qed.
  End path.
End path_natural_transformation.
Ltac path_natural_transformation :=
  repeat match goal with
           | _ => intro
           | _ => apply path_natural_transformation; simpl
         end.

Local Open Scope natural_transformation_scope.
Definition associativityt `{fs : Funext}
           C D F G H I
           (V : @NaturalTransformation C D F G)
           (U : @NaturalTransformation C D G H)
           (T : @NaturalTransformation C D H I)
: (T o U) o V = T o (U o V).
Proof.
  path_natural_transformation.
  apply associativity.
Qed.
Definition functor_category `{Funext} (C D : PreCategory) : PreCategory
  := @Build_PreCategory (Functor C D) (@NaturalTransformation C D) (@composet C D) (@associativityt _ C D).
Notation "C -> D" := (functor_category C D) : category_scope.
Definition NaturalIsomorphism `{Funext} (C D : PreCategory) F G := @Isomorphic (C -> D) F G.
Infix "<~=~>" := NaturalIsomorphism : natural_transformation_scope.
Global Instance isisomorphism_compose' `{Funext}
       `(T' : @NaturalTransformation C D F' F'')
       `(T : @NaturalTransformation C D F F')
       `{@IsIsomorphism (C -> D) F' F'' T'}
       `{@IsIsomorphism (C -> D) F F' T}
: @IsIsomorphism (C -> D) F F'' (T' o T)%natural_transformation
  := @isisomorphism_compose (C -> D) _ _ T' _ _ T _.
Section lemmas.
  Context `{Funext}.
  Variable C : PreCategory.
  Variable F : C -> PreCategory.
  Context
    {w y z}
    {f : Functor (F w) (F z)} {f0 : Functor (F w) (F y)}
    {f2 : Functor (F y) (F z)}
    {f5 : Functor (F w) (F z)}
    {n2 : f <~=~> (f2 o f0)%functor}.
  Lemma p_composition_of_coherent_iso_for_rewrite__isisomorphism_helper' XX
  : @IsIsomorphism
      (F w -> F z) f5 f
      (n2 ^-1 o XX)%natural_transformation.
  Proof.
    eapply isisomorphism_compose'.
    eapply isisomorphism_inverse. (* Toplevel input, characters 22-43:
Error:
In environment
H : Funext
C : PreCategory
F : C -> PreCategory
w : C
y : C
z : C
f : Functor (F w) (F z)
f0 : Functor (F w) (F y)
f2 : Functor (F y) (F z)
f5 : Functor (F w) (F z)
n2 : f <~=~> (f2 o f0)%functor
XX : NaturalTransformation f5 (f2 o f0)
Unable to unify
 "{|
  object := Functor (F w) (F z);
  morphism := NaturalTransformation (D:=F z);
  compose := composet (D:=F z);
  associativity := associativityt (D:=F z) |}" with
 "{|
  object := Functor (F w) (F z);
  morphism := NaturalTransformation (D:=F z);
  compose := composet (D:=F z);
  associativity := associativityt (D:=F z) |}". *)
