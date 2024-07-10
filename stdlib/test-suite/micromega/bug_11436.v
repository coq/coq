From Stdlib Require Import ZArith Lia.
Local Open Scope Z_scope.

Unset Lia Cache.

Goal forall a q q0 q1 r r0 r1: Z,
    0 <= a < 2 ^ 64 ->
    r1 = 4 * q + r ->
    0 <= r < 4 ->
    a = 4 * q0 + r0 ->
    0 <= r0 < 4 ->
    a + 4 = 2 ^ 64 * q1 + r1 ->
    0 <= r1 < 2 ^ 64 ->
    r = r0.
Proof.
  intros.
  (* subst. *)
  Time lia.
Qed.
