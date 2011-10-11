(* This failed with an anomaly in pre-8.4 because of let-in not
   properly taken into account in the test for unification pattern *)

Inductive foo : forall A, A -> Prop :=
| foo_intro : forall A x, foo A x.
Lemma bar A B f : foo (A -> B) f -> forall x : A, foo B (f x).
Fail induction 1.

