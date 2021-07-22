
Theorem type_eq_self@{i j} (A:Type@{i}) (H: A <> A :> Type@{j}) : False.
Proof.
  congruence.
Qed.
