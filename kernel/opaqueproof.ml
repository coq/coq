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

type 'a delayed_universes =
| PrivateMonomorphic of 'a
| PrivatePolymorphic of Univ.ContextSet.t

type opaque_proofterm = cooking_info list * int * (Constr.t * unit delayed_universes) option

type indirect_accessor = {
  access_proof : DirPath.t -> int -> opaque_proofterm;
  access_discharge : cooking_info list -> int -> (Constr.t * unit delayed_universes) -> (Constr.t * unit delayed_universes);
}

let drop_mono = function
| PrivateMonomorphic _ -> PrivateMonomorphic ()
| PrivatePolymorphic _ as ctx -> ctx

type proofterm = (constr * Univ.ContextSet.t delayed_universes) Future.computation
type universes = int

type opaque =
  | Indirect of substitution list * DirPath.t * int (* subst, lib, index *)
  | Direct of universes * cooking_info list * proofterm
type opaquetab = {
  opaque_val : (int * cooking_info list * proofterm) Int.Map.t;
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

let create ~univs cu = Direct (univs, [],cu)

let turn_indirect dp o tab = match o with
  | Indirect (_,_,i) ->
      if not (Int.Map.mem i tab.opaque_val)
      then CErrors.anomaly (Pp.str "Indirect in a different table.")
      else CErrors.anomaly (Pp.str "Already an indirect opaque.")
  | Direct (nunivs, d, cu) ->
    (* Invariant: direct opaques only exist inside sections, we turn them
      indirect as soon as we are at toplevel. At this moment, we perform
      hashconsing of their contents, potentially as a future. *)
      let hcons (c, u) =
        let c = Constr.hcons c in
        let u = match u with
        | PrivateMonomorphic u -> PrivateMonomorphic (Univ.hcons_universe_context_set u)
        | PrivatePolymorphic u -> PrivatePolymorphic (Univ.hcons_universe_context_set u)
        in
        (c, u)
      in
      let cu = Future.chain cu hcons in
      let id = tab.opaque_len in
      let opaque_val = Int.Map.add id (nunivs, d,cu) tab.opaque_val in
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

let discharge_direct_opaque ci = function
  | Indirect _ -> CErrors.anomaly (Pp.str "Not a direct opaque.")
  | Direct (n, d, cu) ->
      Direct (n, ci :: d, cu)

let join except cu = match except with
| None -> ignore (Future.join cu)
| Some except ->
  if Future.UUIDSet.mem (Future.uuid cu) except then ()
  else ignore (Future.join cu)

let join_opaque ?except { opaque_val = prfs; opaque_dir = odp; _ } = function
  | Direct (_,_,cu) -> join except cu
  | Indirect (_,dp,i) ->
      if DirPath.equal dp odp then
        let (_, _, fp) = Int.Map.find i prfs in
        join except fp

let force_proof access { opaque_val = prfs; opaque_dir = odp; _ } = function
  | Direct (n, d, cu) ->
    let (c, u) = Future.force cu in
    access.access_discharge d n (c, drop_mono u)
  | Indirect (l,dp,i) ->
      let c, u =
        if DirPath.equal dp odp
        then
          let (n, d, cu) = Int.Map.find i prfs in
          let (c, u) = Future.force cu in
          access.access_discharge d n (c, drop_mono u)
        else
          let (n, d, cu) = access.access_proof dp i in
          match cu with
          | None -> not_here ()
          | Some (c, u) -> access.access_discharge n d (c, u)
      in
      let c = force_constr (List.fold_right subst_substituted l (from_val c)) in
      (c, u)

let get_mono (_, u) = match u with
| PrivateMonomorphic ctx -> ctx
| PrivatePolymorphic _ -> Univ.ContextSet.empty

let force_constraints _access { opaque_val = prfs; opaque_dir = odp; _ } = function
  | Direct (_,_,cu) ->
    get_mono (Future.force cu)
  | Indirect (_,dp,i) ->
      if DirPath.equal dp odp
      then
        let (_, _, cu) = Int.Map.find i prfs in
        get_mono (Future.force cu)
      else Univ.ContextSet.empty

let get_direct_constraints = function
| Indirect _ -> CErrors.anomaly (Pp.str "Not a direct opaque.")
| Direct (_, _, cu) ->
  Future.chain cu get_mono

module FMap = Future.UUIDMap

let dump ?(except = Future.UUIDSet.empty) { opaque_val = otab; opaque_len = n; _ } =
  let opaque_table = Array.make n ([], 0, None) in
  let f2t_map = ref FMap.empty in
  let iter n (univs, d, cu) =
    let uid = Future.uuid cu in
    let () = f2t_map := FMap.add (Future.uuid cu) n !f2t_map in
    let c =
      if Future.is_val cu then
        let (c, priv) = Future.force cu in
        let priv = match priv with
        | PrivateMonomorphic _ ->
          let () = assert (Int.equal univs 0) in
          PrivateMonomorphic ()
        | PrivatePolymorphic _ as priv -> priv
        in
        Some (c, priv)
      else if Future.UUIDSet.mem uid except then None
      else
        CErrors.anomaly
          Pp.(str"Proof object "++int n++str" is not checked nor to be checked")
    in
    opaque_table.(n) <- (d, univs, c)
  in
  let () = Int.Map.iter iter otab in
  opaque_table, !f2t_map
