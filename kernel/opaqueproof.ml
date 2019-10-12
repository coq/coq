(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
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

type 'a delayed_universes =
| PrivateMonomorphic of 'a
| PrivatePolymorphic of int * Univ.ContextSet.t

type opaque_proofterm = (Constr.t * unit delayed_universes) option

type indirect_accessor = {
  access_proof : DirPath.t -> int -> opaque_proofterm;
  access_discharge : cooking_info list -> (Constr.t * unit delayed_universes) -> (Constr.t * unit delayed_universes);
}

let drop_mono = function
| PrivateMonomorphic _ -> PrivateMonomorphic ()
| PrivatePolymorphic _ as ctx -> ctx

type proofterm = (constr * Univ.ContextSet.t delayed_universes) Future.computation

type opaque =
| Indirect of substitution list * cooking_info list * DirPath.t * int (* subst, discharge, lib, index *)

type opaquetab = {
  opaque_val : proofterm Int.Map.t;
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

let not_here () =
  CErrors.user_err Pp.(str "Cannot access opaque delayed proof")

let create dp cu tab =
  let hcons (c, u) =
    let c = Constr.hcons c in
    let u = match u with
    | PrivateMonomorphic u -> PrivateMonomorphic (Univ.hcons_universe_context_set u)
    | PrivatePolymorphic (n, u) -> PrivatePolymorphic (n, Univ.hcons_universe_context_set u)
    in
    (c, u)
  in
  let cu = Future.chain cu hcons in
  let id = tab.opaque_len in
  let opaque_val = Int.Map.add id cu tab.opaque_val in
  let opaque_dir =
    if DirPath.equal dp tab.opaque_dir then tab.opaque_dir
    else if DirPath.equal tab.opaque_dir DirPath.initial then dp
    else CErrors.anomaly
      (Pp.str "Using the same opaque table for multiple dirpaths.") in
  let ntab = { opaque_val; opaque_dir; opaque_len = id + 1 } in
  Indirect ([], [], dp, id), ntab

let subst_opaque sub = function
| Indirect (s, ci, dp, i) -> Indirect (sub :: s, ci, dp, i)

let discharge_opaque info = function
| Indirect (s, ci, dp, i) ->
  assert (CList.is_empty s);
  Indirect ([], info :: ci, dp, i)

let join except cu = match except with
| None -> ignore (Future.join cu)
| Some except ->
  if Future.UUIDSet.mem (Future.uuid cu) except then ()
  else ignore (Future.join cu)

let join_opaque ?except { opaque_val = prfs; opaque_dir = odp; _ } = function
| Indirect (_,_,dp,i) ->
    if DirPath.equal dp odp then
      let fp = Int.Map.find i prfs in
      join except fp

let force_proof access { opaque_val = prfs; opaque_dir = odp; _ } = function
  | Indirect (l,d,dp,i) ->
      let c, u =
        if DirPath.equal dp odp
        then
          let cu = Int.Map.find i prfs in
          let (c, u) = Future.force cu in
          access.access_discharge d (c, drop_mono u)
        else
          let cu = access.access_proof dp i in
          match cu with
          | None -> not_here ()
          | Some (c, u) -> access.access_discharge d (c, u)
      in
      let c = force_constr (List.fold_right subst_substituted l (from_val c)) in
      (c, u)

let get_mono (_, u) = match u with
| PrivateMonomorphic ctx -> ctx
| PrivatePolymorphic _ -> Univ.ContextSet.empty

let force_constraints _access { opaque_val = prfs; opaque_dir = odp; _ } = function
| Indirect (_,_,dp,i) ->
      if DirPath.equal dp odp
      then
        let cu = Int.Map.find i prfs in
        get_mono (Future.force cu)
      else Univ.ContextSet.empty

module FMap = Future.UUIDMap

let dump ?(except = Future.UUIDSet.empty) { opaque_val = otab; opaque_len = n; _ } =
  let opaque_table = Array.make n None in
  let f2t_map = ref FMap.empty in
  let iter n cu =
    let uid = Future.uuid cu in
    let () = f2t_map := FMap.add (Future.uuid cu) n !f2t_map in
    let c =
      if Future.is_val cu then
        let (c, priv) = Future.force cu in
        let priv = drop_mono priv in
        Some (c, priv)
      else if Future.UUIDSet.mem uid except then None
      else
        CErrors.anomaly
          Pp.(str"Proof object "++int n++str" is not checked nor to be checked")
    in
    opaque_table.(n) <- c
  in
  let () = Int.Map.iter iter otab in
  opaque_table, !f2t_map
