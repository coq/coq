
(* $Id$ *)

(*i*)
open Names
open Term
open Evd
open Environ
open Rawterm
open Evarutil
(*i*)

(* Compilation of pattern-matching. *)

val compile_multcase :
  (trad_constraint -> env -> rawconstr -> unsafe_judgment)
  * 'a evar_defs -> trad_constraint -> env ->
    rawconstr option * rawconstr list *
    (identifier list * pattern list * rawconstr) list ->
    unsafe_judgment
