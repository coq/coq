(* coq-prog-args: ("-skip-qed-typecheck") *)

Lemma bad : False.
Proof. exact_no_check I. Qed.
