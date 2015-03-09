Require Import TestSuite.admit.
Generalizable All Variables.
Definition compose {A B C : Type} (g : B -> C) (f : A -> B) := fun x => g (f x).
Notation "g 'o' f" := (compose g f) (at level 40, left associativity) : function_scope.
Open Scope function_scope.
Axiom ap : forall {A B:Type} (f:A -> B) {x y:A} (p:x = y), f x = f y.
Class IsEquiv {A B : Type} (f : A -> B) := { equiv_inv : B -> A }.
Record Equiv A B := { equiv_fun :> A -> B ; equiv_isequiv :> IsEquiv equiv_fun }.
Notation "A <~> B" := (Equiv A B) (at level 85) : equiv_scope.
Axiom IsHSet : Type -> Type.
Instance isequiv_compose `{IsEquiv A B f} `{IsEquiv B C g} : IsEquiv (compose g f) | 1000.
admit.
Defined.
Set Primitive Projections.
Record hSet := BuildhSet {setT:> Type; iss :> IsHSet setT}.
Canonical Structure default_HSet:= fun T P => (@BuildhSet T P).
Global Instance isequiv_ap_setT X Y : IsEquiv (@ap _ _ setT X Y).
admit.
Defined.
Local Open Scope equiv_scope.
Axiom equiv_path : forall (A B : Type) (p : A = B), A <~> B.

Goal forall (C D : hSet), IsEquiv (fun x : C = D => (equiv_path C D (ap setT x))).
  intros.
  change (IsEquiv (equiv_path C D o @ap _ _ setT C D)).
  apply @isequiv_compose; [ | admit ].
  Set Typeclasses Debug. 
  typeclasses eauto.
