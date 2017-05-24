Unset Strict Universe Declaration.
(* -*- coq-prog-args: ("-nois") -*- *)
(* File reduced by coq-bug-finder from original input, then from 830 lines to 47 lines, then from 25 lines to 11 lines *)
(* coqc version 8.5beta1 (March 2015) compiled on Mar 11 2015 18:51:36 with OCaml 4.01.0
   coqtop version cagnode15:/afs/csail.mit.edu/u/j/jgross/coq-8.5,v8.5 (8dbfee5c5f897af8186cb1bdfb04fd4f88eca677) *)

Declare ML Module "ltac_plugin".

Set Universe Polymorphism.
Class Contr_internal (A : Type) := BuildContr { center : A }.
Arguments center A {_}.
Class Contr (A : Type) : Type := Contr_is_trunc : Contr_internal A.
Hint Extern 0 => progress change Contr_internal with Contr in * : typeclass_instances.
Definition contr_paths_contr0 {A} `{Contr A} : Contr A := {| center := center A |}.
Instance contr_paths_contr1 {A} `{Contr A} : Contr A := {| center := center A |}.
Check @contr_paths_contr0@{i}.
Check @contr_paths_contr1@{i}. (* Error: Universe instance should have length 2 *)
(** It should have length 1, just like contr_paths_contr0 *)
