From Stdlib Require Import Lia ZArith.
Open Scope Z_scope.

Unset Lia Cache.

Axiom word: Type.

(* Expected time < 1.00s *)
Goal forall (right left : Z) (length_xs : nat) (r14 : Z) (v : nat) (x : list word)
   (x2 x1 r8 q2 q r q0 r0 r3 r10 r13 q1 r1 r9 r2 r4 q3 q4
       r5 q5 r6 q6 r7 q7 q8 q9 q10 r11 q11 r12 q12 q13 q14 z83 z84 : Z),
 z84 = 0 ->
 Z.of_nat (Datatypes.length x) - (z83 + 1) <= 0 ->
 z84 = Z.of_nat (Datatypes.length x) - (z83 + 1) ->
 z83 = 0 ->
 q0 <= 0 ->
 0 <= Z.of_nat v ->
 0 <= Z.of_nat length_xs ->
 0 <= Z.of_nat (Datatypes.length x) ->
 Z.of_nat (Datatypes.length x) = Z.of_nat v ->
 r14 < 2 ^ 64 ->
 0 <= r14 ->
 right - left = 2 ^ 64 * q14 + r14 ->
 r13 < 2 ^ 64 ->
 0 <= r13 ->
 r10 - x1 = 2 ^ 64 * q13 + r13 ->
 r12 < 2 ^ 64 ->
 0 <= r12 ->
 q = 2 ^ 64 * q12 + r12 ->
 r11 < 2 ^ 64 ->
 0 <= r11 ->
 r12 * 2 ^ 3 = 2 ^ 64 * q11 + r11 ->
 r10 < 2 ^ 64 ->
 0 <= r10 ->
 x1 + r11 = 2 ^ 64 * q10 + r10 ->
 r9 < 2 ^ 64 ->
 0 <= r9 ->
 r10 + r3 = 2 ^ 64 * q9 + r9 ->
 r8 < 2 ^ 64 ->
 0 <= r8 ->
 x2 - x1 = 2 ^ 64 * q8 + r8 ->
 r7 < 2 ^ 64 ->
 0 <= r7 ->
 Z.shiftr r8 4 = 2 ^ 64 * q7 + r7 ->
 r6 < 2 ^ 64 ->
 0 <= r6 ->
 Z.shiftl r7 3 = 2 ^ 64 * q6 + r6 ->
 r5 < 2 ^ 64 ->
 0 <= r5 ->
 x1 + r6 = 2 ^ 64 * q5 + r5 ->
 r4 < 2 ^ 64 ->
 0 <= r4 ->
 r5 - x1 = 2 ^ 64 * q4 + r4 ->
 r3 < 2 ^ 64 ->
 0 <= r3 ->
 8 = 2 ^ 64 * q3 + r3 ->
 r2 < r3 ->
 0 <= r2 ->
 r4 = r3 * q2 + r2 ->
 r1 < 2 ^ 64 ->
 0 <= r1 ->
 0 < 2 ^ 64 ->
 x2 - r9 = 2 ^ 64 * q1 + r1 ->
 r0 < r3 ->
 0 <= r0 ->
 0 < r3 ->
 r13 = r3 * q0 + r0 ->
 r < 2 ^ 4 ->
 0 <= r ->
 0 < 2 ^ 4 ->
 r8 = 2 ^ 4 * q + r ->
 r8 = 8 * Z.of_nat (Datatypes.length x) ->
 r14 = 8 * Z.of_nat length_xs ->
 (r1 = 8 * z84 -> False) ->
 False.
Proof.
  intros.
  Time lia.
Qed.
