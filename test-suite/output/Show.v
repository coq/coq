(* -*- mode: coq; coq-prog-args: ("-emacs") -*- *)

(* tests of Show output with -emacs flag to coqtop; see bug 5535 *)

Theorem nums : forall (n m : nat), n = m -> (S n) = (S m).
Proof.
  intros.
  induction n as [| n'].  
  induction m as [| m'].
  Show.
Admitted.
