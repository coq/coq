(* -*- mode: coq; coq-prog-args: ("-vos") -*- *)

Axiom axiom : nat.

Lemma foo : nat.
Proof.
  exact axiom.
Qed.

Lemma bar : nat.
Proof.
  exact axiom.
Defined.
