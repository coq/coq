From Stdlib Require Import ZArith Lia.
Local Open Scope Z_scope.

Goal Z.of_N (Z.to_N 0) = 0.
Proof. lia. Qed.

Goal forall q, (Z.of_N (Z.to_N 0) = 0 -> q = 0) -> Z.of_N (Z.to_N 0) = q.
Proof. lia. Qed.
