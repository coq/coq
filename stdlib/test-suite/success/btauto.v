From Stdlib Require Import Btauto.

Open Scope bool_scope.

Lemma test_orb a b : (if a || b then negb (negb b && negb a) else negb a && negb b) = true.
Proof. btauto. Qed.

Lemma test_xorb a : xorb a a = false.
Proof. btauto. Qed.
