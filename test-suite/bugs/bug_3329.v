Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from original input, then from 12095 lines to 869 lines, then from 792 lines to 504 lines, then from 487 lines to 353 lines, then from 258 lines to 174 lines, then from 164 lines to 132 lines, then from 129 lines to 99 lines *)
Set Universe Polymorphism.
Generalizable All Variables.
Axiom admit : forall {T}, T.
Reserved Notation "g 'o' f" (at level 40, left associativity).
Definition compose {A B C : Type} (g : B -> C) (f : A -> B) := fun x => g (f x).
Notation "g 'o' f" := (compose g f).
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a where "x = y" := (@paths _ x y) : type_scope.
Arguments idpath {A a} , [A] a.
Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x) : Type := forall x:A, f x = g x.
Hint Unfold pointwise_paths : typeclass_instances.
Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g)
: forall x, f x = g x
  := fun x => match h with idpath => idpath end.
Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv { equiv_inv : B -> A }.
Class IsHSet (A : Type) := { _ : False }.
Class Funext := { isequiv_apD10 :> forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g) }.
Record PreCategory :=
  { object :> Type;
    morphism : object -> object -> Type;
    trunc_morphism : forall s d, IsHSet (morphism s d) }.

Definition trunc_equiv `(f : A -> B) `{IsHSet A} `{IsEquiv A B f} : IsHSet B := admit.
Global Instance trunc_forall `{Funext} `{P : A -> Type} `{forall a, IsHSet (P a)}
: IsHSet (forall a, P a) | 100.
Proof.
  generalize dependent P.
  intro P.
  assert (f : forall a, P a) by admit.
  assert (g : forall a, P a) by admit.
  pose (@trunc_equiv (forall x : A, @paths (P x) (f x) (g x))
                     (@paths (forall x : A, P x) f g)
                     (@equiv_inv (@paths (forall x : A, P x) f g)
                                 (forall x : A, @paths (P x) (f x) (g x))
                                 (@apD10 A P f g) (@isequiv_apD10 H A P f g))).
  admit.
Defined.
Record Functor (C D : PreCategory) := { object_of :> C -> D }.
Definition identity C : Functor C C := Build_Functor C C admit.
Notation "1" := (identity _) : functor_scope.
Definition functor_category (C D : PreCategory) : PreCategory
  := @Build_PreCategory (Functor C D) admit admit.
Notation "C -> D" := (functor_category C D) : category_scope.
Record hSet := BuildhSet {setT:> Type; iss :> IsHSet setT}.
Global Existing Instance iss.
Definition set_cat `{Funext} : PreCategory :=
  @Build_PreCategory hSet
                     (fun x y => x -> y)
                     _.

Section hom_functor.
  Context `{Funext}.
  Variable C : PreCategory.

  Local Notation obj_of c'c :=
    (BuildhSet
       (morphism
          C
          c'c
          c'c)
       admit).
  Let hom_functor_morphism_of s's d'd (hf : morphism C s's d'd)
  : morphism set_cat (obj_of s's) (obj_of d'd)
    := admit.

  Definition hom_functor : Functor C set_cat := admit.
End hom_functor.
Local Open Scope category_scope.
Local Open Scope functor_scope.
Context `{Funext}.
Variable D : PreCategory.
Set Printing Universes.
Check hom_functor D o 1.
(* Toplevel input, characters 20-44:
Error: Illegal application:
The term "@set_cat" of type "(Funext -> PreCategory)%type"
cannot be applied to the term
 "H" : "Funext"
This term has type "Funext" which should be coercible to
"Funext". *)
(* The command has indeed failed with message:
=> Error: Illegal application:
The term "@set_cat@{Top.345 Top.346 Top.331 Top.332 Top.337 Top.338 Top.339}"
of type
 "(Funext@{Top.346 Top.346 Top.331 Top.332 Top.346} -> PreCategory@{Top.345
   Top.346})%type"
cannot be applied to the term
 "H@{Top.346 Top.330 Top.331 Top.332 Top.333}"
   : "Funext@{Top.346 Top.330 Top.331 Top.332 Top.333}"
This term has type "Funext@{Top.346 Top.330 Top.331 Top.332 Top.333}"
which should be coercible to
 "Funext@{Top.346 Top.346 Top.331 Top.332 Top.346}".
*)
