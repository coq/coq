
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
  env -> 'a evar_defs -> bool -> inductive_family -> constr array

val pred_case_ml_onebranch : env -> 'c evar_map -> bool ->
  inductive_type -> int * constr * constr -> constr 

(*i Utilisés dans Program
val pred_case_ml : env -> 'c evar_map -> bool ->
  constr * (inductive * constr list * constr list)
  ->  constr array -> int * constr  ->constr
val make_case_ml :
  bool -> constr -> constr -> case_info -> constr array -> constr
i*)

(* Compilation of pattern-matching. *)

val compile_cases :
  loc -> (trad_constraint -> env -> rawconstr -> unsafe_judgment)
  * 'a evar_defs -> trad_constraint -> env ->
    rawconstr option * rawconstr list *
    (identifier list * cases_pattern list * rawconstr) list ->
    unsafe_judgment
