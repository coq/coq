
(* $Id$ *)

(*i*)
open Names
open Term
(*i*)

val definition_structure :
  string * identifier * (identifier * Coqast.t) list *
  (bool * (identifier * Coqast.t)) list * identifier *
  Coqast.t -> unit
