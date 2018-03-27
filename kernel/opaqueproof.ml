(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Univ
open Constr
open Mod_subst

type work_list = (Instance.t * Id.t array) Cmap.t * 
  (Instance.t * Id.t array) Mindmap.t

type cooking_info = { 
  modlist : work_list; 
  abstract : Constr.named_context * Univ.Instance.t * Univ.AUContext.t }
type proofterm = (constr * Univ.ContextSet.t) Future.computation
type opaque =
  | Indirect of substitution list * DirPath.t * int (* subst, lib, index *)
  | Direct of cooking_info list * proofterm
type opaquetab = {
  opaque_val : (cooking_info list * proofterm) Int.Map.t;
  (** Actual proof terms *)
  opaque_len : int;
  (** Size of the above map *)
  opaque_dir : DirPath.t;
}
let empty_opaquetab = {
  opaque_val = Int.Map.empty;
  opaque_len = 0;
  opaque_dir = DirPath.initial;
}

(* hooks *)
let default_get_opaque dp _ =
  CErrors.user_err Pp.(pr_sequence str ["Cannot access opaque proofs in library"; DirPath.to_string dp])
let default_get_univ dp _ =
  CErrors.user_err (Pp.pr_sequence Pp.str [
    "Cannot access universe constraints of opaque proofs in library ";
    DirPath.to_string dp])

let get_opaque = ref default_get_opaque
let get_univ = ref default_get_univ

let set_indirect_opaque_accessor f = (get_opaque := f)
let set_indirect_univ_accessor f = (get_univ := f)
(* /hooks *)

let create cu = Direct ([],cu)

let turn_indirect dp o tab = match o with
  | Indirect (_,_,i) ->
      if not (Int.Map.mem i tab.opaque_val)
      then CErrors.anomaly (Pp.str "Indirect in a different table.")
      else CErrors.anomaly (Pp.str "Already an indirect opaque.")
  | Direct (d,cu) ->
      (** Uncomment to check dynamically that all terms turned into
          indirections are hashconsed. *)
(* let check_hcons c = let c' = hcons_constr c in assert (c' == c); c in *)
(* let cu = Future.chain ~pure:true cu (fun (c, u) -> check_hcons c; c, u) in *)
      let id = tab.opaque_len in
      let opaque_val = Int.Map.add id (d,cu) tab.opaque_val in
      let opaque_dir =
        if DirPath.equal dp tab.opaque_dir then tab.opaque_dir
        else if DirPath.equal tab.opaque_dir DirPath.initial then dp
        else CErrors.anomaly
          (Pp.str "Using the same opaque table for multiple dirpaths.") in
      let ntab = { opaque_val; opaque_dir; opaque_len = id + 1 } in
      Indirect ([],dp,id), ntab

let subst_opaque sub = function
  | Indirect (s,dp,i) -> Indirect (sub::s,dp,i)
  | Direct _ -> CErrors.anomaly (Pp.str "Substituting a Direct opaque.")

let iter_direct_opaque f = function
  | Indirect _ -> CErrors.anomaly (Pp.str "Not a direct opaque.")
  | Direct (d,cu) ->
      Direct (d,Future.chain cu (fun (c, u) -> f c; c, u))

let discharge_direct_opaque ~cook_constr ci = function
  | Indirect _ -> CErrors.anomaly (Pp.str "Not a direct opaque.")
  | Direct (d,cu) ->
      Direct (ci::d,Future.chain cu (fun (c, u) -> cook_constr c, u))

let join_opaque { opaque_val = prfs; opaque_dir = odp } = function
  | Direct (_,cu) -> ignore(Future.join cu)
  | Indirect (_,dp,i) ->
      if DirPath.equal dp odp then
        let fp = snd (Int.Map.find i prfs) in
        ignore(Future.join fp)

let uuid_opaque { opaque_val = prfs; opaque_dir = odp } = function
  | Direct (_,cu) -> Some (Future.uuid cu)
  | Indirect (_,dp,i) ->
      if DirPath.equal dp odp
      then Some (Future.uuid (snd (Int.Map.find i prfs)))
      else None

let force_proof { opaque_val = prfs; opaque_dir = odp } = function
  | Direct (_,cu) ->
      fst(Future.force cu)
  | Indirect (l,dp,i) ->
      let pt =
        if DirPath.equal dp odp
        then Future.chain (snd (Int.Map.find i prfs)) fst
        else !get_opaque dp i in
      let c = Future.force pt in
      force_constr (List.fold_right subst_substituted l (from_val c))

let force_constraints { opaque_val = prfs; opaque_dir = odp } = function
  | Direct (_,cu) -> snd(Future.force cu)
  | Indirect (_,dp,i) ->
      if DirPath.equal dp odp
      then snd (Future.force (snd (Int.Map.find i prfs)))
      else match !get_univ dp i with
        | None -> Univ.ContextSet.empty
        | Some u -> Future.force u

let get_constraints { opaque_val = prfs; opaque_dir = odp } = function
  | Direct (_,cu) -> Some(Future.chain cu snd)
  | Indirect (_,dp,i) ->
      if DirPath.equal dp odp
      then Some(Future.chain (snd (Int.Map.find i prfs)) snd)
      else !get_univ dp i

let get_proof { opaque_val = prfs; opaque_dir = odp } = function
  | Direct (_,cu) -> Future.chain cu fst
  | Indirect (l,dp,i) ->
      let pt =
        if DirPath.equal dp odp
        then Future.chain (snd (Int.Map.find i prfs)) fst
        else !get_opaque dp i in
      Future.chain pt (fun c ->
        force_constr (List.fold_right subst_substituted l (from_val c)))
 
module FMap = Future.UUIDMap

let a_constr = Future.from_val (mkRel 1)
let a_univ = Future.from_val Univ.ContextSet.empty
let a_discharge : cooking_info list = []

let dump { opaque_val = otab; opaque_len = n } =
  let opaque_table = Array.make n a_constr in
  let univ_table = Array.make n a_univ in
  let disch_table = Array.make n a_discharge in
  let f2t_map = ref FMap.empty in
  Int.Map.iter (fun n (d,cu) ->
    let c, u = Future.split2 cu in
    Future.sink u;
    Future.sink c;
    opaque_table.(n) <- c;
    univ_table.(n) <- u;
    disch_table.(n) <- d;
    f2t_map := FMap.add (Future.uuid cu) n !f2t_map)
  otab;
  opaque_table, univ_table, disch_table, !f2t_map
