Require Import Setoid.

Parameter F : nat -> nat.
Axiom F_id : forall n : nat, n = F n.
Goal forall n : nat, F n = n.
intro n. setoid_rewrite F_id at 3. reflexivity.
Qed.
