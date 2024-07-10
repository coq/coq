From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Unset Lia Cache.

Goal forall x,
    1 <= x ->
    0 <= x ^ 37.
Proof.
  intros. cbn. (* to bypass `zify` rules for  ^ *)
  lia.
Qed.
