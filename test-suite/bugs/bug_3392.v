Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from original input, then from 12105 lines to 142 lines, then from 83 lines to 57 lines *)
Generalizable All Variables.
Axiom admit : forall {T}, T.
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a where "x = y" := (@paths _ x y) : type_scope.
Arguments idpath {A a} , [A] a.
Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y := match p with idpath => u end.
Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing).
Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y := match p with idpath => idpath end.
Definition apD {A:Type} {B:A->Type} (f:forall a:A, B a) {x y:A} (p:x=y): transport _ p (f x) = f y := admit.
Definition Sect {A B : Type} (s : A -> B) (r : B -> A) := forall x : A, r (s x) = x.
Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
                                               equiv_inv : B -> A ;
                                               eisretr : Sect equiv_inv f;
                                               eissect : Sect f equiv_inv;
                                               eisadj : forall x : A, eisretr (f x) = ap f (eissect x) }.
Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3).
Axiom path_forall : forall {A : Type} {P : A -> Type} (f g : forall x : A, P x), (forall x, f x = g x) -> f = g.
Axiom isequiv_adjointify : forall {A B} (f : A -> B) (g : B -> A) (isretr : Sect g f) (issect : Sect f g), IsEquiv f.
Definition functor_forall `{P : A -> Type} `{Q : B -> Type} (f0 : B -> A) (f1 : forall b:B, P (f0 b) -> Q b)
: (forall a:A, P a) -> (forall b:B, Q b) := (fun g b => f1 _ (g (f0 b))).
Goal forall `{P : A -> Type} `{Q : B -> Type} `{IsEquiv B A f} `{forall b, @IsEquiv (P (f b)) (Q b) (g b)},
       IsEquiv (functor_forall f g).
Proof.
  intros.
  refine (isequiv_adjointify (functor_forall f g)
                             (functor_forall (f^-1)
                                             (fun (x:A) (y:Q (f^-1 x)) => @eisretr _ _ f H x # (g (f^-1 x))^-1 y
                             )) _ _); intros h.
  - abstract (
        apply path_forall; intros b; unfold functor_forall;
        rewrite eisadj;
        admit
      ).
  - abstract (
        apply path_forall; intros a; unfold functor_forall;
        rewrite eissect;
        apply apD
      ).
Defined.
