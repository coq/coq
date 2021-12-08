(* Not considering singleton template-polymorphic inductive types as
   propositions for injection/inversion *)

(* This is also #4560 and #6273 *)

Inductive foo := foo_1.

Goal forall (a b : foo), Some a = Some b -> a = b.
Proof.
  intros a b H.
  inversion H.
  reflexivity.
Qed.

(* Check that Prop is not concerned *)

Inductive bar : Prop := bar_1.

Goal
  forall (a b : bar),
    Some a = Some b ->
    a = b.
Proof.
  intros a b H.
  inversion H.
  Fail reflexivity.
Abort.
