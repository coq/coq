(** JMeq should be polymorphic *)
Require Import JMeq.

Set Implicit Arguments.

Monomorphic Inductive JMeq' (A : Type) (x : A)
: forall B : Type, B -> Prop :=
  JMeq'_refl : JMeq' x x.

(* Note: This should fail (the [Fail] should be present in the final file, even when in bugs/closed) *)
Fail Monomorphic Definition foo := @JMeq' _ (@JMeq').

(* Note: This should not fail *)
Fail Monomorphic Definition bar := @JMeq _ (@JMeq).
