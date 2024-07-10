From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Unset Lia Cache.

From Stdlib Require Import ZArith. Open Scope Z_scope.
From Stdlib Require Import Lia.

Goal forall
    (w0  w1  w2  q0  q : Z)
    (H10 : 0 < w2)
    (q1  q2  r3  q3 : Z)
    (H8 : 0 <= w0)
    (H21 : w1 + - 2 ^ 32 * q2 - 2 ^ 32 * q < 2 ^ 32)
    (H15 : 0 <= w2 * q0 + 0)
    (H4 : w0 - w1 = 2 ^ 32 * q1 + (w2 * q0 + 0))
    (H19 : w2 = 2 ^ 32 * q3 + r3)
    (Hc : w1 + - 2 ^ 32 * q2 - 2 ^ 32 * q > w0)
    (H : q0 <= 0) ,
  False.
Proof.
  intros.
  lia.
Qed.

Goal forall (T : Type) (f : T -> nat) (vs1 : T) (w0 w1 w2 : Z),
    f vs1 = Z.to_nat ((w0 - w1) mod 2 ^ 32 / w2) ->
    ((w0 - w1) mod 2 ^ 32) mod w2 = 0 ->
    0 <= w0 < 2 ^ 32 ->
    0 <= w1 < 2 ^ 32 ->
    0 <= w2 < 2 ^ 32 ->
    (w1 + (w2 mod 2 ^ 32 * Z.of_nat (f vs1)) mod 2 ^ 32) mod 2 ^ 32 = w0.
Proof.
  intros.
  Z.div_mod_to_equations.
  lia.
Qed.
