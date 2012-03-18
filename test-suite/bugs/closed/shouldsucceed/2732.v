(* Check correct behavior of add_primitive_tactic in TACEXTEND *)

(* Added also the case of eauto and congruence *)

Ltac thus H := solve [H].

Lemma test: forall n : nat, n <= n.
Proof.
  intro.
  thus firstorder.
  Undo.
  thus eauto.
Qed.

Lemma test2: false = true -> False.
Proof.
  intro.
  thus congruence.
Qed.
