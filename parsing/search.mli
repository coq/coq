
(*i $Id$ i*)

open Pp
open Term
open Environ
open Pattern

(*s Search facilities. *)

val crible : (std_ppcmds -> env -> constr -> unit) -> global_reference -> unit

val search_by_head : global_reference -> unit

val search_modules : global_reference -> string list * string -> unit
val search_rewrite : Pattern.constr_pattern  -> string list * string -> unit
val search_pattern : Pattern.constr_pattern  -> string list * string -> unit
