Require Import TestSuite.admit.
(* -*- mode: coq; coq-prog-args: ("-indices-matter") *)
(* File reduced by coq-bug-finder from original input, then from 4988 lines to 856 lines, then from 648 lines to 398 lines, then from 401 lines to 332 lines, then from 287 lines to 250 lines, then from 257 lines to 241 lines, then from 223 lines to 175 lines *)
Set Universe Polymorphism.
Set Asymmetric Patterns.
Reserved Notation "g 'o' f" (at level 40, left associativity).
Generalizable All Variables.
Definition admit {T} : T.
Admitted.
Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.
Arguments idpath {A a} , [A] a.
Notation "x = y" := (@paths _ x y) : type_scope.
Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x) : Type
  := forall x:A, f x = g x.
Hint Unfold pointwise_paths : typeclass_instances.
Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.
Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g)
: forall x, f x = g x
  := fun x => match h with idpath => idpath end.

Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv { equiv_inv : B -> A }.

Record Equiv A B := BuildEquiv { equiv_fun :> A -> B ; equiv_isequiv :> IsEquiv equiv_fun }.
Notation "A <~> B" := (Equiv A B) (at level 85) : equiv_scope.

Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3) : equiv_scope.
Class Contr_internal (A : Type) := {}.
Inductive trunc_index : Type :=
| minus_two : trunc_index
| trunc_S : trunc_index -> trunc_index.

Fixpoint IsTrunc_internal (n : trunc_index) (A : Type) : Type :=
  match n with
    | minus_two => Contr_internal A
    | trunc_S n' => forall (x y : A), IsTrunc_internal n' (x = y)
  end.

Class IsTrunc (n : trunc_index) (A : Type) : Type :=
  Trunc_is_trunc : IsTrunc_internal n A.

Instance istrunc_paths (A : Type) n `{H : IsTrunc (trunc_S n) A} (x y : A)
: IsTrunc n (x = y)
  := H x y.

Notation IsHSet := (IsTrunc minus_two).

Class Funext :=
  { isequiv_apD10 :> forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g) }.

Local Open Scope equiv_scope.

Global Instance isequiv_inverse `{IsEquiv A B f} : IsEquiv f^-1 | 10000
  := BuildIsEquiv B A f^-1 f.
Instance trunc_succ `{IsTrunc n A} : IsTrunc (trunc_S n) A | 1000.

admit.

Defined.
Definition trunc_equiv `(f : A -> B)
           `{IsTrunc n A} `{IsEquiv A B f}
: IsTrunc n B.
  admit.
Defined.
Definition trunc_equiv' `(f : A <~> B) `{IsTrunc n A}
: IsTrunc n B
  := admit.
Set Implicit Arguments.
Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Delimit Scope object_scope with object.
Record PreCategory :=
  Build_PreCategory {
      object :> Type;
      morphism : object -> object -> Type;

      identity : forall x, morphism x x;
      compose : forall s d d',
                  morphism d d'
                  -> morphism s d
                  -> morphism s d'
                              where "f 'o' g" := (compose f g);

      associativity : forall x1 x2 x3 x4
                             (m1 : morphism x1 x2)
                             (m2 : morphism x2 x3)
                             (m3 : morphism x3 x4),
                        (m3 o m2) o m1 = m3 o (m2 o m1);

      left_identity : forall a b (f : morphism a b), identity b o f = f;
      right_identity : forall a b (f : morphism a b), f o identity a = f;

      trunc_morphism : forall s d, IsHSet (morphism s d)
    }.
Existing Instance trunc_morphism.

Infix "o" := (@compose _ _ _ _) : morphism_scope.
Delimit Scope functor_scope with functor.

Local Open Scope morphism_scope.
Record Functor (C D : PreCategory) :=
  {
    object_of :> C -> D;
    morphism_of : forall s d, morphism C s d -> morphism D (object_of s) (object_of d)
  }.

(** Workaround to simpl losing universe constraints, see bug #5645. *)
Ltac simpl' :=
  simpl; match goal with [ |- ?P ] => let T := type of P in idtac end.

Global Instance trunc_forall `{Funext} `{P : A -> Type} `{forall a, IsTrunc n (P a)}
: IsTrunc n (forall a, P a) | 100.
Proof.
    generalize dependent P.
  induction n as [ | n' IH]; (simpl'; intros P ?).
  - admit.
  - pose (fun f g => trunc_equiv (@apD10 A P f g) ^-1); admit.
Defined.
Instance trunc_sigma `{P : A -> Type}
         `{IsTrunc n A} `{forall a, IsTrunc n (P a)}
: IsTrunc n (sigT P) | 100.
admit.
Defined.
Record NaturalTransformation C D (F G : Functor C D) :=
  Build_NaturalTransformation' {
      components_of :> forall c, morphism D (F c) (G c)
    }.
Section path_natural_transformation.
  Context `{Funext}.
  Variable C : PreCategory.
  Variable D : PreCategory.
  Variables F G : Functor C D.
  Lemma equiv_sig_natural_transformation
  : { CO : forall x, morphism D (F x) (G x)
    & forall s d (m : morphism C s d),
        CO d o morphism_of F _ _ m = morphism_of G _ _ m o CO s }
      <~> NaturalTransformation F G.

    admit.
  Defined.
  Global Instance trunc_natural_transformation
  : IsHSet (NaturalTransformation F G).
  Proof.
    eapply trunc_equiv'; [ exact equiv_sig_natural_transformation | ].
    typeclasses eauto.
  Qed.
  Lemma path_natural_transformation (T U : NaturalTransformation F G)
  : components_of T == components_of U
    -> T = U.
    admit.
  Defined.
End path_natural_transformation.
Ltac path_natural_transformation :=
  repeat match goal with
           | _ => intro
           | _ => apply path_natural_transformation; simpl
         end.

Section FunctorSectionCategory.
  Context `{Funext}.
  Variable C : PreCategory.
  Variable D : PreCategory.

  Definition category_of_sections : PreCategory.
  Proof.
    refine (@Build_PreCategory
              (Functor D C)
              (fun F G => NaturalTransformation F G)
              admit
              admit
              _
              _
              _
              _);
    abstract (path_natural_transformation; admit).
  Defined. (* Stack overflow *)
