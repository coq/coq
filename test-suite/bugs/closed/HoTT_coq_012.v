(* -*- mode: coq; coq-prog-args: ("-emacs" "-indices-matter") -*- *)

Definition UU := Type.
Inductive toto (B : UU) : UU := c (x : B).
