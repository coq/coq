(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

Symbol T : Type -> Set.

Rewrite Rule TT := T (_ -> nat) => unit.

Goal T (forall A, A).
Proof.
  lazy.
  cbv.
  cbn.
  simpl.
Abort.
