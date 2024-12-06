From Stdlib Require Import Lia ZArith.
Open Scope Z_scope.

Unset Lia Cache.

(* Expected time < 1.00s *)
Goal forall (two64 right left : Z) (length_xs v : nat) (x2 x1 : Z)
            (length_x : nat) (r3 r2 q r r1 q0 r0 q1 q2 q3 : Z),
 two64 = 2 ^ 64 ->
 r3 = 8 * Z.of_nat length_xs ->
 r2 = 8 * Z.of_nat length_x ->
 0 <= 8 * Z.of_nat length_x ->
 8 * Z.of_nat length_x < two64 ->
 r1 = 2 ^ 4 * q + r ->
 0 < 2 ^ 4 ->
 0 <= r ->
 r < 2 ^ 4 ->
 x1 + q * 2 ^ 3 - x1 = two64 * q0 + r0 ->
 0 < two64 ->
 0 <= r0 ->
 r0 < two64 ->
 8 * Z.of_nat length_x = two64 * q1 + r1 ->
 0 <= r1 ->
 r1 < two64 ->
 x2 - x1 = two64 * q2 + r2 ->
 0 <= r2 ->
 r2 < two64 ->
 right - left = two64 * q3 + r3 ->
 0 <= r3 ->
 r3 < two64 ->
 Z.of_nat length_x = Z.of_nat v ->
 0 <= Z.of_nat length_x ->
 0 <= Z.of_nat length_xs ->
 0 <= Z.of_nat v ->
 (r2 = 0 -> False) ->
 (2 ^ 4 = 0 -> False) ->
 (2 ^ 4 < 0 -> False) ->
 (two64 = 0 -> False) ->
 (two64 < 0 -> False) ->
 (r0 < 8 * Z.of_nat length_x -> False) ->
 False.
Proof.
  intros.
  subst.
  Time lia.
Qed.
