(* -*- coq-prog-args: ("-async-proofs" "on"); -*- *)

Unset Universe Polymorphism.

Ltac exact0 := let x := constr:(Type) in exact 0.

Lemma lemma_restrict_abstract@{} : (nat * nat)%type.
Proof. split;[exact 0|abstract exact0]. Qed.
(* Debug: 10237:proofworker:0:0 STM: sending back a fat state
Error: Universe {polymorphism.1} is unbound. *)
