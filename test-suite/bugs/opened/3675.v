Set Primitive Projections.
Definition compose {A B C : Type} (g : B -> C) (f : A -> B) := fun x => g (f x).
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a where "x = y" := (@paths _ x y) : type_scope.
Arguments idpath {A a} , [A] a.
Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z := match p, q with idpath, idpath => idpath end.
Notation "p @ q" := (concat p q) (at level 20) : path_scope.
Axiom ap : forall {A B:Type} (f:A -> B) {x y:A} (p:x = y), f x = f y.
Definition Sect {A B : Type} (s : A -> B) (r : B -> A) := forall x : A, r (s x) = x.
Class IsEquiv {A B : Type} (f : A -> B) := { equiv_inv : B -> A ; eisretr : forall x, f (equiv_inv x) = x }.
Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3, format "f '^-1'") : equiv_scope.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables A B C f g.
Lemma isequiv_compose `{IsEquiv A B f} `{IsEquiv B C g}
: IsEquiv (compose g f).
Proof.
  refine (Build_IsEquiv A C
                        (compose g f)
                        (compose f^-1 g^-1) _).
  exact (fun c => ap g (@eisretr _ _ f _ (g^-1 c)) @ (@eisretr _ _ g _ c)).
