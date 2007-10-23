Require Export NZAxioms.

Set Implicit Arguments.

Module Type NAxiomsSig.
Declare Module Export NZOrdAxiomsMod : NZOrdAxiomsSig.

Delimit Scope NatScope with Nat.
Notation N := NZ.
Notation Neq := NZeq.
Notation N0 := NZ0.
Notation N1 := (NZsucc NZ0).
Notation S := NZsucc.
Notation P := NZpred.
Notation plus := NZplus.
Notation times := NZtimes.
Notation minus := NZminus.
Notation "x == y"  := (NZeq x y) (at level 70) : NatScope.
Notation "x ~= y" := (~ NZeq x y) (at level 70) : NatScope.
Notation "0" := NZ0 : NatScope.
Notation "1" := (NZsucc NZ0) : NatScope.
Notation "x + y" := (NZplus x y) : NatScope.
Notation "x - y" := (NZminus x y) : NatScope.
Notation "x * y" := (NZtimes x y) : NatScope.
Notation "x < y" := (NZlt x y) : NatScope.
Notation "x <= y" := (NZle x y) : NatScope.
Notation "x > y" := (NZlt y x) (only parsing) : NatScope.
Notation "x >= y" := (NZle y x) (only parsing) : NatScope.

Open Local Scope NatScope.

Parameter Inline recursion : forall A : Set, A -> (N -> A -> A) -> N -> A.
Implicit Arguments recursion [A].

Axiom pred_0 : P 0 == 0.

Axiom recursion_wd : forall (A : Set) (Aeq : relation A),
  forall a a' : A, Aeq a a' ->
    forall f f' : N -> A -> A, eq_fun2 Neq Aeq Aeq f f' ->
      forall x x' : N, x == x' ->
        Aeq (recursion a f x) (recursion a' f' x').

Axiom recursion_0 :
  forall (A : Set) (a : A) (f : N -> A -> A), recursion a f 0 = a.

Axiom recursion_succ :
  forall (A : Set) (Aeq : relation A) (a : A) (f : N -> A -> A),
    Aeq a a -> fun2_wd Neq Aeq Aeq f ->
      forall n : N, Aeq (recursion a f (S n)) (f n (recursion a f n)).

End NAxiomsSig.

