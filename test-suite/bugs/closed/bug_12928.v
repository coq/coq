
Lemma test: forall (x:bool) (x: nat), nat.
Proof. intros y x; abstract (exact x). Qed.

Set Mangle Names.
Lemma test': forall x : nat, nat.
Proof. intros x. abstract exact x. Qed.
