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
  declare_global_environment
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

(*let add_thing add kn thing =
  let _,dir,l = repr_kn kn in
  let kn',newenv = add dir l thing !global_env in
    if kn = kn' then
      global_env := newenv
    else
      anomaly "Kernel names do not match."
*)

let add_thing add dir id thing = 
  let kn, newenv = add dir (label_of_id id) thing !global_env in
    global_env := newenv;
    kn

let add_constant = add_thing add_constant 
let add_mind = add_thing add_mind
let add_modtype = add_thing (fun _ -> add_modtype) ()
let add_module = add_thing (fun _ -> add_module) ()

let add_constraints c = global_env := add_constraints c !global_env



let start_module dir id params mtyo =
  let l = label_of_id id in
  let mp,newenv = start_module dir l params mtyo !global_env in
    global_env := newenv;
    mp
  
let end_module id =
  let l = label_of_id id in
  let mp,newenv = end_module l !global_env in
    global_env := newenv;
    mp


let start_modtype dir id params = 
  let l = label_of_id id in
  let mp,newenv = start_modtype dir l params !global_env in
    global_env := newenv;
    mp

let end_modtype id =
  let l = label_of_id id in
  let kn,newenv = end_modtype l !global_env in
    global_env := newenv;
    kn




let lookup_named id = lookup_named id (env())
let lookup_constant kn = lookup_constant kn (env())
let lookup_inductive ind = Inductive.lookup_mind_specif (env()) ind
let lookup_mind kn = lookup_mind kn (env())

let lookup_module mp = lookup_module mp (env())
let lookup_modtype kn = lookup_modtype kn (env())




let start_library dir = 
  let mp,newenv = start_library dir !global_env in
    global_env := newenv; 
    mp

let export s = snd (export !global_env s)

let import cenv digest = 
  let mp,newenv = import cenv digest !global_env in 
    global_env := newenv; 
    mp



(*s Function to get an environment from the constants part of the global
    environment and a given context. *)

let env_of_context hyps = 
  reset_with_named_context hyps (env())

open Libnames

let type_of_reference env = function
  | VarRef id -> let (_,_,t) = Environ.lookup_named id env in t
  | ConstRef c -> Environ.constant_type env c
  | IndRef ind -> Inductive.type_of_inductive env ind
  | ConstructRef cstr -> Inductive.type_of_constructor env cstr

let type_of_global t = type_of_reference (env ()) t


(*let get_kn dp l = 
  make_kn (current_modpath !global_env) dp l
*)
