Require Import Omega.

Lemma test_nat:
  forall n, (5 + pred n <= 5 + n).
Proof.
  intros.
  zify.
  omega.
Qed.

Lemma test_N:
  forall n, (5 + N.pred n <= 5 + n)%N.
Proof.
  intros.
  zify.
  omega.
Qed.
