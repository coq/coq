Require Import Lia ZArith.
Open Scope Z_scope.

Unset Lia Cache.

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
  Time lia. (* used to be 20s *)
Qed.

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
  Time lia. (* used to be 20s *)
Qed.


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
  Time lia.
Qed.

Require Import Lia ZArith.
Open Scope Z_scope.

Unset Lia Cache.

Axiom word: Type.

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

Goal forall (x2 x3 x : Z)
     (H : 0 <= 1073741824 * x + x2 - 67146752)
     (H0 : 0 <= -8192 + x2)
     (H1 : 0 <= 34816 + - x2)
     (H2 : 0 <= -1073741824 * x - x2 + 1073741823),
  False.
Proof.
  intros.
  Time Lia.lia.
Qed.
