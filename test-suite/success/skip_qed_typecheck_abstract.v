(* coq-prog-args: ("-skip-qed-typecheck") *)

(* abstract declares its subproof when the tactic runs, so the kernel still
   checks it. *)
Lemma foo : True.
Proof.
Fail abstract exact_no_check true.
exact I.
Qed.
