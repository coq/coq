(* par! is the easiest way to test UState.union, but it's also used in ssr *)

Axiom S : SProp.

Lemma foo : unit.
Proof.
  pose (T := fun A => A -> A).
  par: pose (K := T S); exact tt.
Qed.

Lemma bar : unit.
Proof.
  pose (T := fun A => A -> A).
  assert unit.
  1:pose (X := S).
  2:pose (X := unit).
  Fail par: (pose (K := T X); exact tt).
Abort.
