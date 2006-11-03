(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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

let env_is_empty () = is_empty !global_env

let _ = 
  declare_summary "Global environment"
    { freeze_function = (fun () -> !global_env);
      unfreeze_function = (fun fr -> global_env := fr);
      init_function = (fun () -> global_env := empty_environment);
      survive_module = true;
      survive_section = false }

(* Then we export the functions of [Typing] on that environment. *)

let universes () = universes (env())
let named_context () = named_context (env())
let named_context_val () = named_context_val (env())

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

let set_engagement c = global_env := set_engagement c !global_env

let start_module id =
  let l = label_of_id id in
  let mp,newenv = start_module l !global_env in
    global_env := newenv;
    mp

let end_module id mtyo =
  let l = label_of_id id in
  let mp,newenv = end_module l mtyo !global_env in
    global_env := newenv;
    mp


let add_module_parameter mbid mte =
  let newenv = add_module_parameter mbid mte !global_env in
    global_env := newenv


let start_modtype id =
  let l = label_of_id id in
  let mp,newenv = start_modtype l !global_env in
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
  | VarRef id -> Environ.named_type id env 
  | ConstRef c -> Typeops.type_of_constant env c
  | IndRef ind ->
     let specif = Inductive.lookup_mind_specif env ind in
      Inductive.type_of_inductive env specif
  | ConstructRef cstr ->
     let specif =
      Inductive.lookup_mind_specif env (inductive_of_constructor cstr) in
       Inductive.type_of_constructor cstr specif

let type_of_global t = type_of_reference (env ()) t
