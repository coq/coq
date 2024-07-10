From Stdlib Require Import Lia ZArith NArith.
Unset Nia Cache.

Open Scope N_scope.


Lemma over (n0 n1 n2 n3 n4 n5 n6 : N)
  (e0 : 1 + 8 * n0 = n1 * n1 + n2)
  (e1 : n1 - 1 = 2 * n3 + n4)
  (e2 : n3 * (1 + n3) = 2 * n5)
  (e3 : n2 + 2 * n4 * n1 - n4 = 8 * n6)
  (o0 : n4 = 0 \/ n4 = 1) :
  n6 = n0 - n5.
Proof.
  Time nia.
Qed.

Lemma over2 (n0 n1 n2 n3 n4 n5 n6 : N)
  (e0 : 1 + 8 * n0 = n1 * n1 + n2)
  (e1 : n1 + 1 = 2 * n3 + n4)
  (e2 : n3 * (1 + n3) = 2 * n5)
  (e3 : n2 + 2 * n4 * n1 + n4 = 8 * n6)
  (o0 : n4 = 0) :
  n6 = n0 + n5.
Proof.
  Fail nia.
Abort.

Open Scope Z_scope.

Lemma over3 (n1 n2 n3 n4 n5 : Z)
  (e : 0 <= n1 /\ 0 <= n2 /\ 0 <= n3 /\ 0 <= n4
   /\ 0 <= n5)
  (e1 : n1 + 1 = 20 * n3 + n4)
  (e3 : n2 + 2 * n4 * n1 + n4 = 8 * n5) :
  n5 = 0.
Proof.
Time Fail nia.
Abort.
