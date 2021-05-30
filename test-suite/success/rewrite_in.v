Require Import Setoid.

Goal forall (P Q : Prop) (f:P->Prop) (p:P), (P<->Q) -> f p -> True.
  intros P Q f p H.
  rewrite H in p || trivial.
Qed.

Goal 1 = 0 -> 0 = 1.
  intro H.
  Fail rewrite H at 1 2 3. (* bug #13566 *)
  Fail rewrite H at 0.
  rewrite H at 1.
  reflexivity.
Qed.
