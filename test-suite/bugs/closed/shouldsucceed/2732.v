(* Check correct behavior of add_primitive_tactic in TACEXTEND *)

Ltac thus H := solve [H].

Lemma test: forall n : nat, n <= n.
Proof.
  intro.
  thus firstorder.
  Undo.
  thus eauto.
Qed.
