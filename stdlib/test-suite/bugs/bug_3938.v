Require Import TestSuite.admit.
From Stdlib Require Import PeanoNat.
#[export] Hint Extern 1 => admit : typeclass_instances.
From Stdlib Require Import Setoid.
Goal forall a b (f : nat -> Set) (R : nat -> nat -> Prop),
       Equivalence R -> R a b -> f a = f b.
  intros a b f H.
  intros. Fail rewrite H1.
Abort.
