From Stdlib Require Import Psatz.
Theorem foo : forall a b, 1 <= S (a + a * S b).
Proof.
intros.
lia.
Qed.
