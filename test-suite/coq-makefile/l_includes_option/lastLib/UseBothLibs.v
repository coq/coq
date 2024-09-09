Require Import Lib1 Lib2.

Lemma use_nat_test_comm : 1 + 2 = 2 + 1.
(* Use a Lemma imported from Lib1 *)
eapply nat_test_comm.
Qed.

Lemma use_xeq : x = x.
(* Use a Lemma imported from Lib2 *)
eapply xeq.
Qed.