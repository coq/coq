(* File reduced by coq-bug-finder from original input, then from 669 lines to 79 lines, then from 89 lines to 44 lines *)
Set Primitive Projections.
Reserved Notation "g 'o' f" (at level 40, left associativity).
Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.
Notation "x = y" := (@paths _ x y) : type_scope.

Set Implicit Arguments.

Record PreCategory :=
  Build_PreCategory' {
      object :> Type;
      morphism : object -> object -> Type;

      identity : forall x, morphism x x;
      compose : forall s d d',
                  morphism d d'
                  -> morphism s d
                  -> morphism s d'
                              where "f 'o' g" := (compose f g);

      left_identity : forall a b (f : morphism a b), identity b o f = f
    }.

Hint Rewrite @left_identity. (* stack overflow *)
