Notation compose := (fun g f x => g (f x)).
Notation "g 'o' f" := (compose g f) (at level 40, left associativity) : function_scope.
Open Scope function_scope.
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a where "x = y" := (@paths _ x y) : type_scope.
Arguments idpath {A a} , [A] a.
Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y := match p with idpath => idpath end.
Class IsEquiv {A B : Type} (f : A -> B) := { equiv_inv : B -> A }.
Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3, format "f '^-1'") : equiv_scope.
Local Open Scope equiv_scope.
Axiom eisretr : forall {A B} (f : A -> B) `{IsEquiv A B f} x, f (f^-1 x) = x.
Generalizable Variables A B C f g.
Global Instance isequiv_compose `{IsEquiv A B f} `{IsEquiv B C g} : IsEquiv (compose g f) | 1000
  := Build_IsEquiv A C (compose g f) (compose f^-1 g^-1).
Definition isequiv_homotopic {A B} (f : A -> B) {g : A -> B} `{IsEquiv A B f} (h : forall x, f x = g x) : IsEquiv g
  := Build_IsEquiv _ _ g (f ^-1).
Global Instance isequiv_inverse {A B} (f : A -> B) `{IsEquiv A B f} : IsEquiv f^-1 | 10000
  := Build_IsEquiv B A f^-1 f.
Definition cancelR_isequiv {A B C} (f : A -> B) {g : B -> C}
  `{IsEquiv A B f} `{IsEquiv A C (g o f)}
  : IsEquiv g.
Proof.
  Unset Typeclasses Modulo Eta.
  exact (isequiv_homotopic (compose (compose g f) f^-1)
                           (fun b => ap g (eisretr f b))) || fail "too early".
  Undo.
  Set Typeclasses Modulo Eta.
  Set Typeclasses Dependency Order.
  Set Typeclasses Debug.
  exact (isequiv_homotopic (compose (compose g f) f^-1)
                           (fun b => ap g (eisretr f b))).
