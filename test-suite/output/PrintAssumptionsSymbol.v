(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)
(** A symbol for rewrite rules is reported as an axiom, and flagged as a symbol. *)
Symbol sym : nat.
Definition uses_sym := sym.
Print Assumptions uses_sym.
Set Printing All Assumptions.
Print Assumptions uses_sym.
