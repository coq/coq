(* -*- mode: coq; coq-prog-args: ("-indices-matter") -*- *)

Definition UU := Type.
Inductive toto (B : UU) : UU := c (x : B).
