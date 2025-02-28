Require Export Stdlib.Setoids.Setoid.

#[projections(primitive=yes)]
Structure Test := {
  test : unit
}.

Axiom tst : Test.
Axiom tst' : Test.
Axiom H : tst = tst'.

Theorem a :
  test tst = test tst'.
Proof.
  setoid_rewrite H.
  exact eq_refl.
  (* The command has indeed failed with message:
     Tactic failure: setoid rewrite failed: Nothing to Qed. *)
Qed.
