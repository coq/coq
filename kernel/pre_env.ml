(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created by Benjamin Grégoire out of environ.ml for better
   modularity in the design of the bytecode virtual evaluation
   machine, Dec 2005 *)
(* Bug fix by Jean-Marc Notin *)

(* This file defines the type of kernel environments *)

open Util
open Names
open Sign
open Univ
open Term
open Declarations

(* The type of environments. *)


type key = int option ref

type constant_key = constant_body * key

type retroknowledge = {
    retro_int31  : (constant * constr) option;
    retro_array  : (constant * constr) option;
    retro_bool   : (constructor * constructor) option; (* true, false *)
    retro_carry  : (constructor * constructor) option; (* C0, C1 *)
    retro_pair   : constructor option;
    retro_cmp    : (constructor * constructor * constructor) option;
                    (* Eq, Lt, Gt *) 
    retro_refl   : constructor option
}

type globals = {
  env_constants : constant_key Cmap_env.t;
  env_inductives : mutual_inductive_body Mindmap_env.t;
  env_modules : module_body MPmap.t;
  env_modtypes : module_type_body MPmap.t}

type stratification = {
  env_universes : universes;
  env_engagement : engagement option
}

type val_kind =
    | VKvalue of values * Idset.t
    | VKnone

type lazy_val = val_kind ref

type named_vals = (identifier * lazy_val) list

type env = {
  env_globals        : globals;
  env_named_context  : named_context;
  env_named_vals     : named_vals;
  env_rel_context    : rel_context;
  env_rel_val        : lazy_val list;
  env_nb_rel         : int;
  env_stratification : stratification;
  env_retroknowledge : retroknowledge
 }

type named_context_val = named_context * named_vals

let empty_named_context_val = [],[]

let empty_retroknowledge = {
    retro_int31 = None;
    retro_array = None;
    retro_bool  = None;
    retro_carry = None;
    retro_pair  = None;
    retro_cmp   = None;
    retro_refl  = None;
}

let empty_env = {
  env_globals = {
    env_constants = Cmap_env.empty;
    env_inductives = Mindmap_env.empty;
    env_modules = MPmap.empty;
    env_modtypes = MPmap.empty};
  env_named_context = empty_named_context;
  env_named_vals = [];
  env_rel_context = empty_rel_context;
  env_rel_val = [];
  env_nb_rel = 0;
  env_stratification = {
    env_universes = initial_universes;
    env_engagement = None };
  env_retroknowledge = empty_retroknowledge
 }


(* Rel context *)

let nb_rel env = env.env_nb_rel

let push_rel d env =
  let rval = ref VKnone in
    { env with
      env_rel_context = add_rel_decl d env.env_rel_context;
      env_rel_val = rval :: env.env_rel_val;
      env_nb_rel = env.env_nb_rel + 1 }

let lookup_rel_val n env =
  try List.nth env.env_rel_val (n - 1)
  with _ -> raise Not_found

let env_of_rel n env =
  { env with
    env_rel_context = Util.list_skipn n env.env_rel_context;
    env_rel_val = Util.list_skipn n env.env_rel_val;
    env_nb_rel = env.env_nb_rel - n
  }

(* Named context *)

let push_named_context_val d (ctxt,vals) =
  let id,_,_ = d in
  let rval = ref VKnone in
    Sign.add_named_decl d ctxt, (id,rval)::vals

exception ASSERT of rel_context

let push_named d env =
(*  if not (env.env_rel_context = []) then raise (ASSERT env.env_rel_context);
  assert (env.env_rel_context = []); *)
  let id,body,_ = d in
  let rval = ref VKnone in
    { env with
      env_named_context = Sign.add_named_decl d env.env_named_context;
      env_named_vals =  (id,rval):: env.env_named_vals }

let lookup_named_val id env =
  snd(List.find (fun (id',_) -> id = id') env.env_named_vals)

(* Warning all the names should be different *)
let env_of_named id env = env

(* Global constants *)

let lookup_constant_key kn env =
  Cmap_env.find kn env.env_globals.env_constants

let lookup_constant kn env =
  fst (Cmap_env.find kn env.env_globals.env_constants)

(* Mutual Inductives *)
let lookup_mind kn env =
  Mindmap_env.find kn env.env_globals.env_inductives

