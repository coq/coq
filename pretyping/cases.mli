
(* $Id$ *)

(*i*)
open Names
open Term
open Evd
open Environ
open Inductive
open Rawterm
open Evarutil
(*i*)

(* Used for old cases in pretyping *)

val branch_scheme : 
  env -> 'a evar_defs -> bool -> int -> inductive_family -> constr

(* Compilation of pattern-matching. *)

val compile_cases :
  (trad_constraint -> env -> rawconstr -> unsafe_judgment)
  * 'a evar_defs -> trad_constraint -> env ->
    rawconstr option * rawconstr list *
    (identifier list * cases_pattern list * rawconstr) list ->
    unsafe_judgment
