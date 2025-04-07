Require Export Corelib.Setoids.Setoid.

Module Test1.

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

End Test1.

Module Test2.

#[projections(primitive=yes)]
Structure Test (n : nat) := {
  test : unit
}.

Axiom tst : Test 0.
Axiom tst' : Test 0.
Axiom H : tst = tst'.

Theorem a :
  test _ tst = test _ tst'.
Proof.
  setoid_rewrite H.
  exact eq_refl.
Qed.

End Test2.

Module Test3.

#[projections(primitive=yes)]
Structure Test (n : nat) := {
  test : unit
}.

Axiom n : nat.
Axiom tst : Test n.
Axiom tst' : Test n.
Axiom H : n = 0.

Theorem a :
  test _ tst = test _ tst'.
Proof.
  Fail setoid_rewrite H. (* no rewriting in parameters *)
Abort.

End Test3.
