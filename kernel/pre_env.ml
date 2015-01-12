(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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
open Context
open Univ
open Term
open Declarations

(* The type of environments. *)

(* The key attached to each constant is used by the VM to retrieve previous *)
(* evaluations of the constant. It is essentially an index in the symbols table *)
(* used by the VM. *)
type key = int Ephemeron.key option ref 

(** Linking information for the native compiler. *)

type link_info =
  | Linked of string
  | LinkedInteractive of string
  | NotLinked

type constant_key = constant_body * (link_info ref * key)

type mind_key = mutual_inductive_body * link_info ref

type globals = {
  env_constants : constant_key Cmap_env.t;
  env_inductives : mind_key Mindmap_env.t;
  env_modules : module_body MPmap.t;
  env_modtypes : module_type_body MPmap.t}

type stratification = {
  env_universes : universes;
  env_engagement : engagement option;
  env_type_in_type : bool
}

type val_kind =
    | VKvalue of (values * Id.Set.t) Ephemeron.key
    | VKnone

type lazy_val = val_kind ref

let force_lazy_val vk = match !vk with
| VKnone -> None
| VKvalue v -> try Some (Ephemeron.get v) with Ephemeron.InvalidKey -> None

let dummy_lazy_val () = ref VKnone
let build_lazy_val vk key = vk := VKvalue (Ephemeron.create key)

type named_vals = (Id.t * lazy_val) list

type env = {
  env_globals       : globals;
  env_named_context : named_context;
  env_named_vals    : named_vals;
  env_rel_context   : rel_context;
  env_rel_val       : lazy_val list;
  env_nb_rel        : int;
  env_stratification : stratification;
  env_conv_oracle   : Conv_oracle.oracle;
  retroknowledge : Retroknowledge.retroknowledge;
  indirect_pterms : Opaqueproof.opaquetab;
}

type named_context_val = named_context * named_vals

let empty_named_context_val = [],[]

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
    env_engagement = None;
    env_type_in_type = false};
  env_conv_oracle = Conv_oracle.empty;
  retroknowledge = Retroknowledge.initial_retroknowledge;
  indirect_pterms = Opaqueproof.empty_opaquetab }


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
  with Failure _ -> raise Not_found

let env_of_rel n env =
  { env with
    env_rel_context = Util.List.skipn n env.env_rel_context;
    env_rel_val = Util.List.skipn n env.env_rel_val;
    env_nb_rel = env.env_nb_rel - n
  }

(* Named context *)

let push_named_context_val d (ctxt,vals) =
  let id,_,_ = d in
  let rval = ref VKnone in
    add_named_decl d ctxt, (id,rval)::vals

let push_named d env =
(*  if not (env.env_rel_context = []) then raise (ASSERT env.env_rel_context);
  assert (env.env_rel_context = []); *)
  let id,body,_ = d in
  let rval = ref VKnone in
  { env_globals = env.env_globals;
    env_named_context = Context.add_named_decl d env.env_named_context;
    env_named_vals = (id, rval) :: env.env_named_vals;
    env_rel_context = env.env_rel_context;
    env_rel_val = env.env_rel_val;
    env_nb_rel = env.env_nb_rel;
    env_stratification = env.env_stratification;
    env_conv_oracle = env.env_conv_oracle;
    retroknowledge = env.retroknowledge;
    indirect_pterms = env.indirect_pterms;
  }

let lookup_named_val id env =
  snd(List.find (fun (id',_) -> Id.equal id id') env.env_named_vals)

(* Warning all the names should be different *)
let env_of_named id env = env

(* Global constants *)

let lookup_constant_key kn env =
  Cmap_env.find kn env.env_globals.env_constants

let lookup_constant kn env =
  fst (Cmap_env.find kn env.env_globals.env_constants)

(* Mutual Inductives *)
let lookup_mind kn env =
  fst (Mindmap_env.find kn env.env_globals.env_inductives)

let lookup_mind_key kn env =
  Mindmap_env.find kn env.env_globals.env_inductives
