Goal forall B C : nat -> nat -> Prop, forall k, C 0 k ->
  (exists A, (forall k', C A k' -> B A k') -> B A k).
Proof.
  intros B C k H.
  econstructor.
  intros X.
  apply X.
  apply H.
Qed.

