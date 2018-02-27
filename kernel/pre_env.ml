(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Benjamin Grégoire out of environ.ml for better
   modularity in the design of the bytecode virtual evaluation
   machine, Dec 2005 *)
(* Bug fix by Jean-Marc Notin *)

(* This file defines the type of kernel environments *)

open Util
open Names
open Declarations

module NamedDecl = Context.Named.Declaration

(* The type of environments. *)

(* The key attached to each constant is used by the VM to retrieve previous *)
(* evaluations of the constant. It is essentially an index in the symbols table *)
(* used by the VM. *)
type key = int CEphemeron.key option ref 

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
  env_universes : UGraph.t;
  env_engagement : engagement
}

type val_kind =
    | VKvalue of (Vmvalues.values * Id.Set.t) CEphemeron.key
    | VKnone

type lazy_val = val_kind ref

let force_lazy_val vk = match !vk with
| VKnone -> None
| VKvalue v -> try Some (CEphemeron.get v) with CEphemeron.InvalidKey -> None

let dummy_lazy_val () = ref VKnone
let build_lazy_val vk key = vk := VKvalue (CEphemeron.create key)

type named_context_val = {
  env_named_ctx : Context.Named.t;
  env_named_map : (Context.Named.Declaration.t * lazy_val) Id.Map.t;
}

type rel_context_val = {
  env_rel_ctx : Context.Rel.t;
  env_rel_map : (Context.Rel.Declaration.t * lazy_val) Range.t;
}

type env = {
  env_globals       : globals;           (* globals = constants + inductive types + modules + module-types *)
  env_named_context : named_context_val; (* section variables *)
  env_rel_context   : rel_context_val;
  env_nb_rel        : int;
  env_stratification : stratification;
  env_typing_flags  : typing_flags;
  retroknowledge : Retroknowledge.retroknowledge;
  indirect_pterms : Opaqueproof.opaquetab;
}

let empty_named_context_val = {
  env_named_ctx = [];
  env_named_map = Id.Map.empty;
}

let empty_rel_context_val = {
  env_rel_ctx = [];
  env_rel_map = Range.empty;
}

let empty_env = {
  env_globals = {
    env_constants = Cmap_env.empty;
    env_inductives = Mindmap_env.empty;
    env_modules = MPmap.empty;
    env_modtypes = MPmap.empty};
  env_named_context = empty_named_context_val;
  env_rel_context = empty_rel_context_val;
  env_nb_rel = 0;
  env_stratification = {
    env_universes = UGraph.initial_universes;
    env_engagement = PredicativeSet };
  env_typing_flags = Declareops.safe_flags Conv_oracle.empty;
  retroknowledge = Retroknowledge.initial_retroknowledge;
  indirect_pterms = Opaqueproof.empty_opaquetab }


(* Rel context *)

let nb_rel env = env.env_nb_rel

let push_rel_context_val d ctx = {
  env_rel_ctx = Context.Rel.add d ctx.env_rel_ctx;
  env_rel_map = Range.cons (d, ref VKnone) ctx.env_rel_map;
}

let match_rel_context_val ctx = match ctx.env_rel_ctx with
| [] -> None
| decl :: rem ->
  let (_, lval) = Range.hd ctx.env_rel_map in
  let ctx = { env_rel_ctx = rem; env_rel_map = Range.tl ctx.env_rel_map } in
  Some (decl, lval, ctx)

let push_rel d env =
    { env with
      env_rel_context = push_rel_context_val d env.env_rel_context;
      env_nb_rel = env.env_nb_rel + 1 }

let lookup_rel n env =
  try fst (Range.get env.env_rel_context.env_rel_map (n - 1))
  with Invalid_argument _ -> raise Not_found

let lookup_rel_val n env =
  try snd (Range.get env.env_rel_context.env_rel_map (n - 1))
  with Invalid_argument _ -> raise Not_found

let rel_skipn n ctx = {
  env_rel_ctx = Util.List.skipn n ctx.env_rel_ctx;
  env_rel_map = Range.skipn n ctx.env_rel_map;
}

let env_of_rel n env =
  { env with
    env_rel_context = rel_skipn n env.env_rel_context;
    env_nb_rel = env.env_nb_rel - n
  }

(* Named context *)

let push_named_context_val_val d rval ctxt =
(*   assert (not (Id.Map.mem (NamedDecl.get_id d) ctxt.env_named_map)); *)
  {
    env_named_ctx = Context.Named.add d ctxt.env_named_ctx;
    env_named_map = Id.Map.add (NamedDecl.get_id d) (d, rval) ctxt.env_named_map;
  }

let push_named_context_val d ctxt =
  push_named_context_val_val d (ref VKnone) ctxt

let match_named_context_val c = match c.env_named_ctx with
| [] -> None
| decl :: ctx ->
  let (_, v) = Id.Map.find (NamedDecl.get_id decl) c.env_named_map in
  let map = Id.Map.remove (NamedDecl.get_id decl) c.env_named_map in
  let cval = { env_named_ctx = ctx; env_named_map = map } in
  Some (decl, v, cval)

let map_named_val f ctxt =
  let open Context.Named.Declaration in
  let fold accu d =
    let d' = map_constr f d in
    let accu =
      if d == d' then accu
      else Id.Map.modify (get_id d) (fun _ (_, v) -> (d', v)) accu
    in
    (accu, d')
  in
  let map, ctx = List.fold_left_map fold ctxt.env_named_map ctxt.env_named_ctx in
  if map == ctxt.env_named_map then ctxt
  else { env_named_ctx = ctx; env_named_map = map }

let push_named d env =
  {env with env_named_context = push_named_context_val d env.env_named_context}

let lookup_named id env =
  fst (Id.Map.find id env.env_named_context.env_named_map)

let lookup_named_val id env =
  snd(Id.Map.find id env.env_named_context.env_named_map)

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
