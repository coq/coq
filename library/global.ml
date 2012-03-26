(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Errors
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
      init_function = (fun () -> global_env := empty_environment) }

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


let add_thing add dir id thing =
  let kn, newenv = add dir (label_of_id id) thing !global_env in
    global_env := newenv;
    kn

let add_constant = add_thing add_constant
let add_mind = add_thing add_mind
let add_modtype x y inl = add_thing (fun _ x y -> add_modtype x y inl) () x y


let add_module id me inl =
  let l = label_of_id id in
  let mp,resolve,new_env = add_module l me inl !global_env in
    global_env := new_env;
    mp,resolve
    

let add_constraints c = global_env := add_constraints c !global_env

let set_engagement c = global_env := set_engagement c !global_env

let add_include me is_module inl =
  let resolve,newenv = add_include me is_module inl !global_env in
    global_env := newenv;
    resolve

let start_module id =
  let l = label_of_id id in
  let mp,newenv = start_module l !global_env in
    global_env := newenv;
    mp

let end_module fs id mtyo =
  let l = label_of_id id in
  let mp,resolve,newenv = end_module l mtyo !global_env in
    Summary.unfreeze_summaries fs;
    global_env := newenv;
    mp,resolve


let add_module_parameter mbid mte inl =
  let resolve,newenv = add_module_parameter mbid mte inl !global_env in
    global_env := newenv;
    resolve


let start_modtype id =
  let l = label_of_id id in
  let mp,newenv = start_modtype l !global_env in
    global_env := newenv;
    mp

let end_modtype fs id =
  let l = label_of_id id in
  let kn,newenv = end_modtype l !global_env in
    Summary.unfreeze_summaries fs;
    global_env := newenv;
    kn

let pack_module () = 
  pack_module !global_env



let lookup_named id = lookup_named id (env())
let lookup_constant kn = lookup_constant kn (env())
let lookup_inductive ind = Inductive.lookup_mind_specif (env()) ind
let lookup_mind kn = lookup_mind kn (env())

let lookup_module mp = lookup_module mp (env())
let lookup_modtype kn = lookup_modtype kn (env())

let constant_of_delta_kn kn =
  let resolver,resolver_param = (delta_of_senv !global_env) in
  (* TODO : are resolver and resolver_param orthogonal ?
     the effect of resolver is lost if resolver_param isn't
     trivial at that spot. *)
    Mod_subst.constant_of_delta resolver_param
      (Mod_subst.constant_of_delta_kn resolver kn)

let mind_of_delta_kn kn =
  let resolver,resolver_param = (delta_of_senv !global_env) in
  (* TODO idem *)
    Mod_subst.mind_of_delta resolver_param
      (Mod_subst.mind_of_delta_kn resolver kn)

let exists_objlabel id = exists_objlabel id !global_env

let start_library dir =
  let mp,newenv = start_library dir !global_env in
    global_env := newenv;
    mp

let export s = export !global_env s

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


(* spiwack: register/unregister functions for retroknowledge *)
let register field value by_clause =
  let entry = kind_of_term value in
  let senv = Safe_typing.register !global_env field entry by_clause in
  global_env := senv


