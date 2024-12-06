
Require Import Corelib.Setoids.Setoid Corelib.Classes.Morphisms.

Class PartialOrder {A} (R : relation A) : Prop := {
  partial_order_pre :: PreOrder R;
}.
Global Hint Mode PartialOrder - ! : typeclass_instances.

Axiom Permutation : forall {A:Type}, list A -> list A -> Prop.

Infix "≡ₚ" := Permutation (at level 70, no associativity).

Global Declare Instance Permutation_cons A :
 Proper (Logic.eq ==> @Permutation A ==> @Permutation A) (@cons A) | 7.
(* priority < 7 does not trigger the bug *)

Global Declare Instance Permutation_Equivalence A : Equivalence (@Permutation A).

Lemma bla A (x:A) (lc lc' lac lbc : list A) (Hc: lac ++ lbc ≡ₚ lc') (HH:x :: lc' ≡ₚ lc)
  : True /\ x :: lac ++ lbc ≡ₚ lc.
Proof.
  rewrite Hc.
  auto.
Qed.
