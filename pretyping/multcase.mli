
(* $Id$ *)

open Names
open Term
open Evd
open Environ
open Rawterm
open Evarutil

(* used by trad.ml *)
val compile_multcase :
  (trad_constraint -> unsafe_env -> rawconstr -> unsafe_judgment)
  * 'a evar_defs -> trad_constraint -> unsafe_env ->
    rawconstr option * rawconstr list *
    (identifier list * pattern list * rawconstr) list ->
    unsafe_judgment
