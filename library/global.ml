(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util
open Names
open Term
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
      survive_section = false }

(* Then we export the functions of [Typing] on that environment. *)

let universes () = universes (env())
let named_context () = named_context (env())

let push_named_assum a =
  let (cst,env) = push_named_assum a !global_env in
  global_env := env;
  cst
let push_named_def d =
  let (cst,env) = push_named_def d !global_env in
  global_env := env;
  cst

let add_constant sp ce = global_env := add_constant sp ce !global_env
let add_mind sp mie = global_env := add_mind sp mie !global_env
let add_constraints c = global_env := add_constraints c !global_env

let lookup_named id = lookup_named id (env())
let lookup_constant sp = lookup_constant sp (env())
let lookup_inductive ind = Inductive.lookup_mind_specif (env()) ind
let lookup_mind sp = lookup_mind sp (env())

let export s = export !global_env s
let import cenv = global_env := import cenv !global_env

(*s Function to get an environment from the constants part of the global
    environment and a given context. *)

let env_of_context hyps = 
  reset_with_named_context hyps (env())

open Nametab

let type_of_reference env = function
  | VarRef id -> let (_,_,t) = Environ.lookup_named id env in t
  | ConstRef c -> Environ.constant_type env c
  | IndRef ind -> Inductive.type_of_inductive env ind
  | ConstructRef cstr -> Inductive.type_of_constructor env cstr

let type_of_global t = type_of_reference (env ()) t
