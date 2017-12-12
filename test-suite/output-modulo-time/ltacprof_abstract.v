(* -*- coq-prog-args: ("-profile-ltac-cutoff" "0.0") -*- *)
Ltac sleep' := do 100 (do 100 (do 100 idtac)).
Ltac sleep := sleep'.

Theorem x : True.
Proof.
  idtac. idtac. abstract (sleep; constructor).
Defined.
