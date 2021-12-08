Require Import TestSuite.admit.
Axiom transport : forall {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x), P y.
Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing).
Definition Sect {A B : Type} (s : A -> B) (r : B -> A) := forall x : A, r (s x) = x.
Class IsEquiv {A B} (f : A -> B) := { equiv_inv : B -> A ; eisretr : Sect equiv_inv f }.
Arguments eisretr {A B} f {_} _.
Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3, format "f '^-1'").
Generalizable Variables A B f g e n.
Definition functor_forall `{P : A -> Type} `{Q : B -> Type}
           (f0 : B -> A) (f1 : forall b:B, P (f0 b) -> Q b)
: (forall a:A, P a) -> (forall b:B, Q b).
  admit.
Defined.

Lemma isequiv_functor_forall `{P : A -> Type} `{Q : B -> Type}
      `{IsEquiv B A f} `{forall b, @IsEquiv (P (f b)) (Q b) (g b)}
: (forall b : B, Q b) -> forall a : A, P a.
Proof.
  refine (functor_forall
            (f^-1)
            (fun (x:A) (y:Q (f^-1 x)) => eisretr f x # (g (f^-1 x))^-1 y)).
Defined. (* was: Error: Attempt to save an incomplete proof *)
