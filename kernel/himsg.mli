
(* $Id$ *)

(*i*)
open Pp
open Names
open Term
open Sign
open Environ
(*i*)

val error_unbound_rel : path_kind -> 'a unsafe_env -> int -> 'b

val error_cant_execute : path_kind -> 'a unsafe_env -> constr -> 'b
