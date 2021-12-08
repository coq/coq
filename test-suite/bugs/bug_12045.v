(* Check enough reduction happens in the conclusion of an induction scheme *)

Lemma foo :
  forall (P : nat -> Prop),
    (forall n, P (S n)) ->
    forall n,
      (fun e =>
         IsSucc e ->
         P e) n.
Proof.
Admitted.

Theorem bar : forall n,
    IsSucc n ->
    True.
Proof.
  intros.
  Fail induction n using foo. (* was an anomaly *)
Admitted.
