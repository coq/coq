
(* $Id$ *)

open Names
open Term

val definition_structure :
  string * identifier * (identifier * CoqAst.t) list *
  (bool * (identifier * CoqAst.t)) list * identifier *
  CoqAst.t -> unit;;

(* $Id$ *)
