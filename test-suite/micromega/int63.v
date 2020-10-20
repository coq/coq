Require Import ZArith ZifyInt63 Lia.
Require Import Int63.

Open Scope int63_scope.

Goal forall (x:int), 0 <= x = true.
Proof. lia. Qed.

Goal max_int = 9223372036854775807.
Proof. lia. Qed.

Goal digits = 63.
Proof. lia. Qed.

Goal wB = (2^63)%Z.
Proof. lia. Qed.

Goal forall x y, x + y <= max_int = true.
Proof. lia. Qed.

Goal forall x, x <> 0 -> x / x = 1.
Proof.
  nia.
Qed.
