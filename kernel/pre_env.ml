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
open Sign
open Univ
open Term
open Declarations

(* The type of environments. *)


type key = int option ref 

type constant_key = constant_body * key
 
type globals = {
  env_constants : constant_key Cmap.t;
  env_inductives : mutual_inductive_body KNmap.t;
  env_modules : module_body MPmap.t;
  env_modtypes : module_type_body KNmap.t }

type stratification = {
  env_universes : universes;
  env_engagement : engagement option
}

type 'a val_kind =   
  | VKvalue of values
  | VKaxiom of 'a
  | VKdef of constr

type 'a lazy_val = 'a val_kind ref

type rel_val = inv_rel_key lazy_val

type named_val = identifier lazy_val

type named_vals = (identifier * named_val) list

type env = {
  env_globals       : globals;
  env_named_context : named_context;
  env_named_vals    : named_vals;
  env_rel_context   : rel_context;
  env_rel_val       : rel_val list;
  env_nb_rel        : int;
  env_stratification : stratification }

type named_context_val = named_context * named_vals

let empty_named_context_val = [],[]

let empty_env = { 
  env_globals = {
    env_constants = Cmap.empty;
    env_inductives = KNmap.empty;
    env_modules = MPmap.empty;
    env_modtypes = KNmap.empty };
  env_named_context = empty_named_context;
  env_named_vals = [];
  env_rel_context = empty_rel_context;
  env_rel_val = [];
  env_nb_rel = 0;
  env_stratification = {
    env_universes = initial_universes;
    env_engagement = None } }


(* Rel context *)

let nb_rel env = env.env_nb_rel

let push_rel d env =
  let _,body,_ = d in
  let rval =
    match body with
    | None -> ref (VKaxiom env.env_nb_rel)
    | Some c -> ref (VKdef c)
  in     
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
  let id,body,_ = d in
  let rval =
    match body with
    | None -> ref (VKaxiom id)
    | Some c -> ref (VKdef c)
  in Sign.add_named_decl d ctxt, (id,rval)::vals

exception ASSERT of Sign.rel_context

let push_named d env = 
(*  if not (env.env_rel_context = []) then raise (ASSERT env.env_rel_context);
  assert (env.env_rel_context = []); *)
  let id,body,_ = d in
  let rval =
    match body with
    | None -> ref (VKaxiom id)
    | Some c -> ref (VKdef c)
  in
  { env with  
    env_named_context = Sign.add_named_decl d env.env_named_context;
    env_named_vals =  (id,rval):: env.env_named_vals }

let lookup_named_val id env =
   snd(List.find (fun (id',_) -> id = id') env.env_named_vals)
  
(* Warning all the names should be different *)
let env_of_named id env = env
 
(* Global constants *)

let lookup_constant_key kn env =
  Cmap.find kn env.env_globals.env_constants

let lookup_constant kn env =
  fst (Cmap.find kn env.env_globals.env_constants)

(* Mutual Inductives *)
let lookup_mind kn env =
  KNmap.find kn env.env_globals.env_inductives
