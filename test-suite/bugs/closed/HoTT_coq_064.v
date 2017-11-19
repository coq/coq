Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from 279 lines to 219 lines. *)

Set Implicit Arguments.
Set Universe Polymorphism.
Definition admit {T} : T.
Admitted.
Module Export Overture.
  Reserved Notation "g 'o' f" (at level 40, left associativity).

  Inductive paths {A : Type} (a : A) : A -> Type :=
    idpath : paths a a.

  Arguments idpath {A a} , [A] a.

  Notation "x = y :> A" := (@paths A x y) : type_scope.

  Notation "x = y" := (x = y :>_) : type_scope.

  Delimit Scope path_scope with path.

  Local Open Scope path_scope.

  Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y
    := match p with idpath => idpath end.

  Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g)
  : forall x, f x = g x
    := fun x => match h with idpath => idpath end.

  Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv { equiv_inv : B -> A }.

  Delimit Scope equiv_scope with equiv.
  Local Open Scope equiv_scope.

  Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3) : equiv_scope.

  Class Funext.
  Axiom isequiv_apD10 : `{Funext} -> forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g) .
  Existing Instance isequiv_apD10.

  Definition path_forall `{Funext} {A : Type} {P : A -> Type} (f g : forall x : A, P x) :
    (forall x, f x = g x) -> f = g
    :=
      (@apD10 A P f g)^-1.

End Overture.

Module Export Core.

  Set Implicit Arguments.
  Delimit Scope morphism_scope with morphism.
  Delimit Scope category_scope with category.
  Delimit Scope object_scope with object.

  Record PreCategory :=
    {
      object :> Type;
      morphism : object -> object -> Type;

      compose : forall s d d',
                  morphism d d'
                  -> morphism s d
                  -> morphism s d'
                              where "f 'o' g" := (compose f g);

      associativity : forall x1 x2 x3 x4
                             (m1 : morphism x1 x2)
                             (m2 : morphism x2 x3)
                             (m3 : morphism x3 x4),
                        (m3 o m2) o m1 = m3 o (m2 o m1)
    }.
  Bind Scope category_scope with PreCategory.
  Arguments compose [!C%category s%object d%object d'%object] m1%morphism m2%morphism : rename.

  Infix "o" := compose : morphism_scope.

End Core.

Local Open Scope morphism_scope.
Record Functor (C D : PreCategory) :=
  {
    object_of :> C -> D;
    morphism_of : forall s d, morphism C s d
                              -> morphism D (object_of s) (object_of d)
  }.

Inductive Unit : Set :=
  tt : Unit.

Definition indiscrete_category (X : Type) : PreCategory
  := @Build_PreCategory X
                        (fun _ _ => Unit)
                        (fun _ _ _ _ _ => tt)
                        (fun _ _ _ _ _ _ _ => idpath).


Record NaturalTransformation C D (F G : Functor C D) := { components_of :> forall c, morphism D (F c) (G c) }.
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
    : (forall x, T x = U x)
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
Definition comma_category A B C (S : Functor A C) (T : Functor B C)
: PreCategory.
  admit.
Defined.
Definition compose C D (F F' F'' : Functor C D)
           (T' : NaturalTransformation F' F'') (T : NaturalTransformation F F')
: NaturalTransformation F F''
  := Build_NaturalTransformation F F''
                                 (fun c => T' c o T c).

Infix "o" := compose : natural_transformation_scope.

Local Open Scope natural_transformation_scope.

Definition associativity `{fs : Funext}
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
  := @Build_PreCategory (Functor C D)
                        (@NaturalTransformation C D)
                        (@compose C D)
                        (@associativity _ C D).

Notation "C -> D" := (functor_category C D) : category_scope.

Definition compose_functor `{Funext} (C D E : PreCategory) : object ((C -> D) -> ((D -> E) -> (C -> E))).
  admit.

Defined.

Definition pullback_along `{Funext} (C C' D : PreCategory) (p : Functor C C')
: object ((C' -> D) -> (C -> D))
  := Eval hnf in compose_functor _ _ _ p.

Definition IsColimit `{Funext} C D (F : Functor D C) 
           (x : object
                  (@comma_category (indiscrete_category Unit)
                                   (@functor_category H (indiscrete_category Unit) C)
                                   (@functor_category H D C)
                                   admit
                                   (@pullback_along H D (indiscrete_category Unit) C
                                                    admit))) : Type
  := admit.

Generalizable All Variables.
Axiom fs : Funext.
Existing Instance fs.

Section bar.

  Variable D : PreCategory.

  Context `(has_colimits
            : forall F : Functor D C,
                @IsColimit _ C D F (colimits F)).
(* Error: Unsatisfied constraints: Top.3773 <= Set
 (maybe a bugged tactic). *)
End bar.
