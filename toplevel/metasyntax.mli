
(* $Id$ *)

(*i*)
open Extend
(*i*)

(* Adding grammar and pretty-printing objects in the environment *)

val add_syntax_obj : string -> Coqast.t list -> unit

val add_grammar_obj : string -> Coqast.t list -> unit
val add_token_obj : string -> unit

val add_infix : Gramext.g_assoc option -> int -> string -> string -> unit
val add_distfix : Gramext.g_assoc option -> int -> string -> string -> unit

val print_grammar : string -> string -> unit
