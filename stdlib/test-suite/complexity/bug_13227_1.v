From Stdlib Require Import Lia ZArith.
Open Scope Z_scope.

Unset Lia Cache.

(* Expected time < 1.00s *)
Goal forall Y r0 r q q0 r1 q1 : Z,
    3 = 4294967296 * q1 + r1 ->
    Y - r1 = 4294967296 * q0 + r0 ->
    r1 < 4294967296 ->
    0 <= r1 ->
    r0 < 4294967296 ->
    0 <= r0 ->
    r < 4 ->
    0 <= r ->
    0 < 4 ->
    r0 = 4 * q + r ->
    Y < 4294967296 ->
    0 <= Y ->
    r = 0 ->
    r0 < 268517376 ->
    268513280 <= r0 ->
    268587008 <= Y ->
    False.
Proof.
  intros.
  Time lia.
Qed.
