Require Import TestSuite.admit.
(* This failed with an anomaly in pre-8.4 because of let-in not
   properly taken into account in the test for unification pattern *)

Inductive foo : forall A, A -> Prop :=
| foo_intro : forall A x, foo A x.
Lemma bar A B f : foo (A -> B) f -> forall x : A, foo B (f x).
Fail induction 1.

(* Whether these examples should succeed with a non-dependent return predicate 
   or fail because there is well-typed return predicate dependent in f 
   is questionable. As of 25 oct 2011, they succeed *)
refine (fun p => match p with _ => _ end).
Undo.
refine (fun p => match p with foo_intro _ _ => _ end).
admit.
Qed.
