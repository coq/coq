
(*i $Id$ i*)

open Pp
open Names
open Term
open Environ
open Pattern

(*s Search facilities. *)

val search_by_head : global_reference -> dir_path list * bool -> unit
val search_rewrite : constr_pattern -> dir_path list * bool -> unit
val search_pattern : constr_pattern -> dir_path list * bool -> unit
