Goal forall A B, A * B -> A.
Proof.
intros A B H.
match goal with
  | [ H : _ * _ |- _ ] => exact (fst H)
end.
Qed.
