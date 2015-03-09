Require Import TestSuite.admit.
Definition foo : Set.
Proof.
  refine ($(abstract admit)$).
Qed.
