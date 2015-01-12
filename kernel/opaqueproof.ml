(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Univ
open Term
open Mod_subst

type work_list = (Instance.t * Id.t array) Cmap.t * 
  (Instance.t * Id.t array) Mindmap.t

type cooking_info = { 
  modlist : work_list; 
  abstract : Context.named_context * Univ.universe_level_subst * Univ.UContext.t } 
type proofterm = (constr * Univ.universe_context_set) Future.computation
type opaque =
  | Indirect of substitution list * DirPath.t * int (* subst, lib, index *)
  | Direct of cooking_info list * proofterm
type opaquetab = (cooking_info list * proofterm) Int.Map.t * DirPath.t
let empty_opaquetab = Int.Map.empty, DirPath.initial

(* hooks *)
let default_get_opaque dp _ =
  Errors.error
    ("Cannot access opaque proofs in library " ^ DirPath.to_string dp)
let default_get_univ dp _ =
  Errors.error
    ("Cannot access universe constraints of opaque proofs in library " ^
    DirPath.to_string dp)

let get_opaque = ref default_get_opaque
let get_univ = ref default_get_univ

let set_indirect_opaque_accessor f = (get_opaque := f)
let set_indirect_univ_accessor f = (get_univ := f)
(* /hooks *)

let create cu = Direct ([],cu)

let turn_indirect dp o (prfs,odp) = match o with
  | Indirect _ -> Errors.anomaly (Pp.str "Already an indirect opaque")
  | Direct (d,cu) ->
      let cu = Future.chain ~pure:true cu (fun (c, u) -> hcons_constr c, u) in
      let id = Int.Map.cardinal prfs in
      let prfs = Int.Map.add id (d,cu) prfs in
      let ndp =
        if DirPath.equal dp odp then odp
        else if DirPath.equal odp DirPath.initial then dp
        else Errors.anomaly
          (Pp.str "Using the same opaque table for multiple dirpaths") in
      Indirect ([],dp,id), (prfs, ndp)

let subst_opaque sub = function
  | Indirect (s,dp,i) -> Indirect (sub::s,dp,i)
  | Direct _ -> Errors.anomaly (Pp.str "Substituting a Direct opaque")

let iter_direct_opaque f = function
  | Indirect _ -> Errors.anomaly (Pp.str "Not a direct opaque")
  | Direct (d,cu) ->
      Direct (d,Future.chain ~pure:true cu (fun (c, u) -> f c; c, u))

let discharge_direct_opaque ~cook_constr ci = function
  | Indirect _ -> Errors.anomaly (Pp.str "Not a direct opaque")
  | Direct (d,cu) ->
      Direct (ci::d,Future.chain ~pure:true cu (fun (c, u) -> cook_constr c, u))

let join_opaque (prfs,odp) = function
  | Direct (_,cu) -> ignore(Future.join cu)
  | Indirect (_,dp,i) ->
      if DirPath.equal dp odp then
        let fp = snd (Int.Map.find i prfs) in
        ignore(Future.join fp)

let uuid_opaque (prfs,odp) = function
  | Direct (_,cu) -> Some (Future.uuid cu)
  | Indirect (_,dp,i) ->
      if DirPath.equal dp odp
      then Some (Future.uuid (snd (Int.Map.find i prfs)))
      else None

let force_proof (prfs,odp) = function
  | Direct (_,cu) ->
      fst(Future.force cu)
  | Indirect (l,dp,i) ->
      let pt =
        if DirPath.equal dp odp
        then Future.chain ~pure:true (snd (Int.Map.find i prfs)) fst
        else !get_opaque dp i in
      let c = Future.force pt in
      force_constr (List.fold_right subst_substituted l (from_val c))

let force_constraints (prfs,odp) = function
  | Direct (_,cu) -> snd(Future.force cu)
  | Indirect (_,dp,i) ->
      if DirPath.equal dp odp
      then snd (Future.force (snd (Int.Map.find i prfs)))
      else match !get_univ dp i with
        | None -> Univ.ContextSet.empty
        | Some u -> Future.force u

let get_constraints (prfs,odp) = function
  | Direct (_,cu) -> Some(Future.chain ~pure:true cu snd)
  | Indirect (_,dp,i) ->
      if DirPath.equal dp odp
      then Some(Future.chain ~pure:true (snd (Int.Map.find i prfs)) snd)
      else !get_univ dp i

let get_proof (prfs,odp) = function
  | Direct (_,cu) -> Future.chain ~pure:true cu fst
  | Indirect (l,dp,i) ->
      let pt =
        if DirPath.equal dp odp
        then Future.chain ~pure:true (snd (Int.Map.find i prfs)) fst
        else !get_opaque dp i in
      Future.chain ~pure:true pt (fun c ->
        force_constr (List.fold_right subst_substituted l (from_val c)))
 
module FMap = Future.UUIDMap

let a_constr = Future.from_val (Term.mkRel 1)
let a_univ = Future.from_val Univ.ContextSet.empty
let a_discharge : cooking_info list = []

let dump (otab,_) =
  let n = Int.Map.cardinal otab in
  let opaque_table = Array.make n a_constr in
  let univ_table = Array.make n a_univ in
  let disch_table = Array.make n a_discharge in
  let f2t_map = ref FMap.empty in
  Int.Map.iter (fun n (d,cu) ->
    let c, u = Future.split2 ~greedy:true cu in
    Future.sink u;
    Future.sink c;
    opaque_table.(n) <- c;
    univ_table.(n) <- u;
    disch_table.(n) <- d;
    f2t_map := FMap.add (Future.uuid cu) n !f2t_map)
  otab;
  opaque_table, univ_table, disch_table, !f2t_map
