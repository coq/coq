Require Export Corelib.Setoids.Setoid.

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
Qed.
