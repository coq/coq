
(* $Id$ *)

open Util
(* open Generic *)
open Term
open Instantiate
open Sign
open Safe_typing
open Summary

(* We introduce here the global environment of the system, and we declare it
   as a synchronized table. *)

let global_env = ref empty_environment

let safe_env () = !global_env

let env () = env_of_safe_env !global_env

let _ = 
  declare_summary "Global environment"
    { freeze_function = (fun () -> !global_env);
      unfreeze_function = (fun fr -> global_env := fr);
      init_function = (fun () -> global_env := empty_environment) }

(* Then we export the functions of [Typing] on that environment. *)

let universes () = universes !global_env
let context () = context !global_env
let var_context () = var_context !global_env

let push_var_def idc = global_env := push_var_def idc !global_env
let push_var_decl idc = global_env := push_var_decl idc !global_env
(*
let push_rel_def nac = global_env := push_rel nac !global_env
let push_rel_decl nac = global_env := push_rel nac !global_env
*)
let add_constant sp ce = global_env := add_constant sp ce !global_env
let add_parameter sp c = global_env := add_parameter sp c !global_env
let add_mind sp mie = global_env := add_mind sp mie !global_env
let add_constraints c = global_env := add_constraints c !global_env

let pop_vars ids = global_env := pop_vars ids !global_env

let lookup_var id = lookup_var id !global_env
(*
let lookup_rel n = lookup_rel n !global_env
*)
let lookup_constant sp = lookup_constant sp !global_env
let lookup_mind sp = lookup_mind sp !global_env
let lookup_mind_specif c = lookup_mind_specif c !global_env

let export s = export !global_env s
let import cenv = global_env := import cenv !global_env

(* Some instanciations of functions from [Environ]. *)

let id_of_global id = Environ.id_of_global (env_of_safe_env !global_env) id

(* Functions of [Inductive], composed with [lookup_mind_specif]. *)
(* Rem:Cannot open Inductive to avoid clash with Inductive.lookup_mind_specif*)

let mind_is_recursive =
  Util.compose Inductive.mis_is_recursive lookup_mind_specif 

let mind_nconstr = Util.compose Inductive.mis_nconstr lookup_mind_specif
let mind_nparams = Util.compose Inductive.mis_nparams lookup_mind_specif
let mind_nf_arity x =
  body_of_type (Inductive.mis_user_arity (lookup_mind_specif x))
let mind_nf_lc = Util.compose Inductive.mis_nf_lc lookup_mind_specif


