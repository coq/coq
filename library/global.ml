
(* $Id$ *)

open Util
open Names
open Term
open Instantiate
open Sign
open Environ
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
      init_function = (fun () -> global_env := empty_environment);
      survive_section = true }

(* Then we export the functions of [Typing] on that environment. *)

let universes () = universes !global_env
let context () = context !global_env
let named_context () = named_context !global_env

let push_named_def idc = global_env := push_named_def idc !global_env
let push_named_assum idc = global_env := push_named_assum idc !global_env

let add_parameter sp c = global_env := add_parameter sp c !global_env
let add_constant sp ce = global_env := add_constant sp ce !global_env
let add_discharged_constant sp r = 
  global_env := add_discharged_constant sp r !global_env
let add_mind sp mie = global_env := add_mind sp mie !global_env
let add_constraints c = global_env := add_constraints c !global_env

let pop_named_decls ids = global_env := pop_named_decls ids !global_env

let lookup_named id = lookup_named id !global_env
let lookup_constant sp = lookup_constant sp !global_env
let lookup_mind sp = lookup_mind sp !global_env
let lookup_mind_specif c = lookup_mind_specif c !global_env

let set_opaque sp = set_opaque !global_env sp
let set_transparent sp = set_transparent !global_env sp

let export s = export !global_env s
let import cenv = global_env := import cenv !global_env

(* Some instanciations of functions from [Environ]. *)

let sp_of_global id = Environ.sp_of_global (env_of_safe_env !global_env) id

(* To know how qualified a name should be to be understood in the current env*)

let is_visible ref qid = (Nametab.locate qid = ref)

let qualid_of_global ref =  
  let sp = sp_of_global ref in
  let qid = make_qualid [] (string_of_id (basename sp)) in
  if is_visible ref qid then qid
  else make_qualid (dirpath sp) (string_of_id (basename sp))

(*s Function to get an environment from the constants part of the global
    environment and a given context. *)

let env_of_context hyps = 
  change_hyps (fun _ -> hyps) (env_of_safe_env !global_env)

(* Functions of [Inductive], composed with [lookup_mind_specif]. *)
(* Rem:Cannot open Inductive to avoid clash with Inductive.lookup_mind_specif*)

let mind_is_recursive =
  Util.compose Inductive.mis_is_recursive lookup_mind_specif 

let mind_nconstr = Util.compose Inductive.mis_nconstr lookup_mind_specif
let mind_nparams = Util.compose Inductive.mis_nparams lookup_mind_specif
let mind_nf_arity x =
  body_of_type (Inductive.mis_user_arity (lookup_mind_specif x))
let mind_nf_lc = Util.compose Inductive.mis_nf_lc lookup_mind_specif


