(* -*- mode: coq; coq-prog-args: ("-indices-matter") -*- *)
Set Universe Polymorphism.
Set Printing Universes.
Inductive Empty : Set := .
(* Toplevel input, characters 15-41:
Error: Universe inconsistency. Cannot enforce Prop <= Set). *)
