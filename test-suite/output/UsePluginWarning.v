(* -*- mode: coq; coq-prog-args: ("-w" "-extraction-logical-axiom") -*- *)
Require Extraction.
Axiom foo : Prop.

Extraction foo.

