(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

Symbol raise : forall A, A.

Rewrite Rule raise_pi := raise (forall (x : ?A), ?B) => fun (x : ?A) => raise ?B.

Goal (raise (nat -> nat -> Prop) 0 0).
  hnf.
  Fail progress hnf.
  match goal with |- raise Prop => idtac end.
  apply raise.
Qed.
