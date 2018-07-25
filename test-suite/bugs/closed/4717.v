(* Lia being smarter on recognizing nat and Z *)

Require Import Lia Zify.

Definition nat' := nat.

Theorem le_not_eq_lt : forall (n m:nat),
    n <= m ->
    n <> m :> nat' ->
    n < m.
Proof.
  intros.
  lia.
Qed.

Goal forall (x n : nat'), x = x + n - n.
Proof.
  intros.
  lia.
Qed.

Require Import ZArith Lia.

Open Scope Z_scope.

Definition Z' := Z.

Theorem Zle_not_eq_lt : forall n m,
    n <= m ->
    n <> m :> Z' ->
    n < m.
Proof.
  intros.
  lia.
  Undo.
  lia.
Qed.
