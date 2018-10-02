Goal (forall T : Type, T = T) -> Type.
Proof.
  intro H.
  Fail specialize (H _).
Abort.
