(* File reduced by coq-bug-finder from original input, then from 7372 lines to 539 lines, then from 531 lines to 107 lines, then from 76 lines to 46 lines *)
Module First.
Set Asymmetric Patterns.
Reserved Notation "x -> y" (at level 99, right associativity, y at level 200).
Notation "A -> B" := (forall (_ : A), B).
Set Universe Polymorphism.


Notation "x → y" := (x -> y)
  (at level 99, y at level 200, right associativity): type_scope.
Record sigT A (P : A -> Type) :=
  { projT1 : A ; projT2 : P projT1 }.
Arguments projT1 {A P} s.
Arguments projT2 {A P} s.
Definition compose {A B C : Type} (g : B -> C) (f : A -> B) := fun x => g (f x).
Reserved Notation "x = y" (at level 70, no associativity).
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a where "x = y" := (@paths _ x y).
Notation " x = y " := (paths x y) : type_scope.
Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y := match p with idpath => u end.
Reserved Notation "{ x : A  & P }" (at level 0, x at level 99).
Notation "{ x : A  & P }" := (sigT A (fun x => P)) : type_scope.


Axiom path_sigma_uncurried : forall {A : Type} (P : A -> Type) (u v : sigT A P) (pq : {p : projT1 u = projT1 v &  transport _ p (projT2 u) = projT2 v}), u = v.
Axiom isequiv_pr1_contr : forall {A} {P : A -> Type}, (A -> {x : A & P x}).

Definition path_sigma_hprop {A : Type} {P : A -> Type} (u v : sigT _ P) :=
  @compose _ _ _ (path_sigma_uncurried P u v) (@isequiv_pr1_contr _ _).
End First.

Set Asymmetric Patterns.
Set Universe Polymorphism.
Arguments projT1 {_ _} _.
Notation "( x ; y )" := (existT _ x y).
Notation pr1 := projT1.
Notation "x .1" := (projT1 x) (at level 3).
Notation "x .2" := (projT2 x) (at level 3).
Definition compose {A B C : Type} (g : B -> C) (f : A -> B) := fun x => g (f x).
Notation "g 'o' f" := (compose g f) (at level 40, left associativity).
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a where "x = y" := (@paths _ x y) : type_scope.
Arguments idpath {A a} , [A] a.
Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y := match p with idpath => u end.
Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing).
Class IsEquiv {A B : Type} (f : A -> B) := { equiv_inv : B -> A }.
Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3).
Axiom path_sigma_uncurried : forall {A : Type} (P : A -> Type) (u v : sigT P) (pq : {p : u.1 = v.1 &  p # u.2 = v.2}), u = v.
Instance isequiv_pr1_contr {A} {P : A -> Type} : IsEquiv (@pr1 A P) | 100.
Admitted.

Definition path_sigma_hprop {A : Type} {P : A -> Type} (u v : sigT P) : u.1 = v.1 -> u = v := 
  path_sigma_uncurried P u v o pr1^-1.
