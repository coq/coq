Require Import TestSuite.admit.
Definition foo : Set.
Proof.
  refine (ltac:(abstract admit)).
Qed.
