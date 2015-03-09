Require Import TestSuite.admit.
Require Import Coq.Arith.PeanoNat.
Hint Extern 1 => admit : typeclass_instances.
Require Import Setoid.
Goal forall a b (f : nat -> Set) (R : nat -> nat -> Prop), 
       Equivalence R -> R a b -> f a = f b.
  intros a b f H.
  intros. Fail rewrite H1. 
