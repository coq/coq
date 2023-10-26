(* -*- coq-prog-args: ("-async-proofs" "on" "-async-proofs-tac-j" "1"); -*- *)

Lemma foo (A B : Prop) n : n + 0 = n /\ (A -> B -> A).
Proof. split. par: now auto. Qed.
