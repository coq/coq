Require Import A B.

Definition z := x + y.

Lemma zeq : z = z.
Proof. pose xeq. pose yeq. auto. Qed.

Lemma yeq'' : y = y.
Proof. apply yeq'. Admitted.

Module M. Include B.M. End M.
Module T. Include B.T. End T.
Module F. Include B.F. End F.
