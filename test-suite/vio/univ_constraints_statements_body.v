Definition T := Type.
Definition T1 : T := Type.

Lemma x : True.
Proof.
exact (let a : T := Type in I).
Qed.
