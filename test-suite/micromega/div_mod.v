Require Import ZArith Lia ZifyNat.

(* regression observed in PR 14037 *)
Goal forall (n:nat), n mod 2 < 2 -> n mod 2 = 0 \/ n mod 2 = 1.
Proof. lia. Qed.

(* regression observed in PR 14037 *)
Goal forall (n:nat), n / 2 < 2 -> n / 2 = 0 \/ n / 2 = 1.
Proof. lia. Qed.

Goal forall (n:nat), n mod 2 = 0 \/ n mod 2 = 1.
Proof. lia. Qed.

Goal forall (n:nat), n / 2 < 2 -> n / 2 = 0 \/ n / 2 = 1.
Proof. lia. Qed.

Goal forall (n:nat), (n * 3) mod 3 = 0.
Proof. lia. Qed.

Goal forall (n:nat), (n * 3) / 3 = n.
Proof. lia. Qed.

Goal forall (m n:nat), m > 0 -> (n * m) / m = n.
Proof. nia. Qed.

(* just nia is not strong enough in 8.14 *)
Goal forall (m n:nat), m > 0 -> (n * m) mod m = 0.
Proof.
  Fail nia. (* if this suceeds, please update test *)
  intros.
  cut ((n * m) / m = n); nia.
Qed.

Goal forall (n m:nat), 1 <= (1+n)^m.
Proof. lia. Qed.
