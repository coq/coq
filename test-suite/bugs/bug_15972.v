Search True. (* Ok *)
Goal True.
Proof.
  Search True. (* Ok *)
  exact I.
  Search True. (* [Focus] No such goal. *)
Qed.
Search True. (* Ok *)

Goal True /\ True.
Proof.
  split.
  - exact I.
    Search True. (* [Focus] No such goal *)
Abort.
