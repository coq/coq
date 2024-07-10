From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Sint63.
From Stdlib Require ZifySint63.

Open Scope sint63_scope.

Goal forall (x : int), -4611686018427387904 <=? x = true.
Proof. lia. Qed.

Goal max_int = 4611686018427387903.
Proof. lia. Qed.

Goal digits = 63.
Proof. lia. Qed.

Goal wB = (2^63)%Z.
Proof. lia. Qed.

Goal forall x y, x + y <=? max_int = true.
Proof. lia. Qed.

Goal forall x y z, x + 3 * y - z - y = x + 2 * y - z.
Proof. lia. Qed.

Goal forall x, x <> 0 -> x / x = 1.
Proof. nia. Qed.

Goal min_int / -1 = min_int.
Proof. lia. Qed.

Goal forall x y, is_zero x = true -> 3 * x + y = y.
Proof. lia. Qed.

Goal forall x, 0 <=? x = true -> abs x = x.
Proof. lia. Qed.

Goal forall x, x <? 0 = true -> abs x = - x.
Proof. lia. Qed.

Goal forall x, x <> min_int -> 0 <=? abs x = true.
Proof. lia. Qed.
