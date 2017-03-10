(* -*- mode: coq; coq-prog-args: ("-emacs" "-w" "-extraction-logical-axiom") -*- *)

Require Extraction.
Axiom foo : Prop.

Extraction foo.

