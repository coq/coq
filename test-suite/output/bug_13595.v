Inductive Cube:Set :=| Triple: nat -> nat -> nat -> Cube.

Theorem incomplete :forall a b c d : nat,Triple a = Triple b->Triple d c = Triple d b->a = c.
Proof.
  Fail congruence.
  intros.
  congruence with ((Triple a a a)) ((Triple d c a)).
Qed.
