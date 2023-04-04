
Module M.
  Private Inductive foo := .

  Definition to_nat (f:foo) : nat := match f with end.
End M.

Lemma bar : False.
Proof.
  exact_no_check I.
  Fail Validate Proof.
Abort.

Lemma bar f : M.to_nat f = 0.
Proof.
  Validate Proof.

  cbv.

  Fail Validate Proof.

Abort.
