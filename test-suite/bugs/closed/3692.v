Reserved Notation "x -> y" (at level 99, right associativity, y at level 200).
Reserved Notation "x = y" (at level 70, no associativity).
Reserved Notation "x * y" (at level 40, left associativity).
Delimit Scope core_scope with core.
Open Scope core_scope.
Notation "A -> B" := (forall (_ : A), B) : type_scope.
Global Set Primitive Projections.
Global Set Implicit Arguments.
Record prod (A B : Type) := pair { fst : A ; snd : B }.
Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a where "x = y" := (@paths _ x y) : type_scope.
Definition Sect {A B : Type} (s : A -> B) (r : B -> A) := forall x : A, r (s x) = x.
Class IsEquiv {A B : Type} (f : A -> B) := { equiv_inv : B -> A ; eisretr : Sect equiv_inv f }.
Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3, format "f '^-1'").
Generalizable Variables X A B f g n.
Axiom path_prod' : forall {A B : Type} {x x' : A} {y y' : B}, (x = x') -> (y = y') -> ((x,y) = (x',y')).
Definition functor_prod {A A' B B' : Type} (f:A->A') (g:B->B')
: A * B -> A' * B'.
  exact (fun z => (f (fst z), g (snd z))).
Defined.
Definition isequiv_functor_prod `{IsEquiv A A' f} `{IsEquiv B B' g}
: IsEquiv (functor_prod f g)
  := @Build_IsEquiv
       _ _ (functor_prod f g) (functor_prod f^-1 g^-1)
       (fun z => path_prod' (@eisretr _ _ f _ (fst z)) (@eisretr _ _ g _ (snd z))).
