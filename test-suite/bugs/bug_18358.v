CoInductive P : nat -> Prop :=
  | Pintro : forall n, P 0 -> P 0 -> P (S n) -> P n.

Lemma P_any : forall n, P n.
Proof.
  cofix IH. intros.
  assert (H: P 0). { apply IH. }  Guarded. (*Guarded: anomaly*)
  apply Pintro. { apply H. } { apply H. } { apply IH. }
Qed. (*Guard checker happy *)
