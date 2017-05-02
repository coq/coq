(* -*- mode: coq; coq-prog-args: ("-indices-matter") -*- *)
Set Universe Polymorphism.
Set Printing Universes.
Inductive Empty : Set := .
(* Error: Universe inconsistency. Cannot enforce Prop <= Set). *)
