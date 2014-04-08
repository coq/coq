(** JMeq should be polymorphic *)
Require Import JMeq.

Set Implicit Arguments.

Monomorphic Inductive JMeq' (A : Type) (x : A)
: forall B : Type, B -> Prop :=
  JMeq'_refl : JMeq' x x.

Fail Monomorphic Definition foo := @JMeq' _ (@JMeq').

Monomorphic Definition bar := @JMeq _ (@JMeq).
