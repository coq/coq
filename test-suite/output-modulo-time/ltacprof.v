(* -*- coq-prog-args: ("-emacs" "-profile-ltac" "-compile" "output-modulo-time/PLACEHOLDER.v") -*- *)
Ltac sleep' := do 100 (do 100 (do 100 idtac)).
Ltac sleep := sleep'.

Theorem x : True.
Proof.
  idtac. idtac. sleep. constructor.
Defined.
