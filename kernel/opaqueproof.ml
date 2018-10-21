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

(************************************************************************)
(** {6 Tables of opaque proof terms} *)

(** We now store opaque proof terms apart from the rest of the environment.
    See the [Indirect] contructor in [Lazyconstr.lazy_constr]. This way,
    we can quickly load a first half of a .vo file without these opaque
    terms, and access them only when a specific command (e.g. Print or
    Print Assumptions) needs it. *)

(** Delayed / available tables of opaque terms *)

type disk_data = Constr.t Future.computation array Delayed.t

module LibraryOrdered = DirPath
module LibraryMap = Map.Make(LibraryOrdered)

module DiskData = struct

  type t = disk_data LibraryMap.t
  let empty = LibraryMap.empty

  let add dp d map = LibraryMap.add dp d map

  let memo_table : Constr.t Future.computation array LibraryMap.t ref = ref LibraryMap.empty

  (* Resistant to Marshall / workers *)
  let fetch dp map =
    try LibraryMap.find dp !memo_table
    with Not_found ->
      let pp_dp = DirPath.print dp in
      let delayed_data = LibraryMap.find dp map in
      try
        Flags.if_verbose Feedback.(msg_info ?loc:None) Pp.(str"Fetching opaque tables from disk for " ++ pp_dp);
        let fetch_data = Delayed.fetch delayed_data in
        memo_table := LibraryMap.add dp fetch_data !memo_table;
        fetch_data
      with Delayed.Faulty f ->
        CErrors.user_err ~hdr:"Library.access_table"
          Pp.(str "The file " ++ str f ++ str " (bound to " ++ pp_dp ++
              str ") is inaccessible or corrupted,\ncannot load some opaque tables in it." ++ fnl ())

end

(** Work lists for cooking *)

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

let join_opaque { opaque_val = prfs; opaque_dir = odp; _ } = function
  | Direct (_,cu) -> ignore(Future.join cu)
  | Indirect (_,dp,i) ->
      if DirPath.equal dp odp then
        let fp = snd (Int.Map.find i prfs) in
        ignore(Future.join fp)

let uuid_opaque { opaque_val = prfs; opaque_dir = odp; _ } = function
  | Direct (_,cu) -> Some (Future.uuid cu)
  | Indirect (_,dp,i) ->
      if DirPath.equal dp odp
      then Some (Future.uuid (snd (Int.Map.find i prfs)))
      else None

let access_table tables dp i =
  let t = DiskData.fetch dp tables in
  assert (i < Array.length t);
  t.(i)

let get_opaque otbl dp i =
  access_table otbl dp i

let force_cst tbl { opaque_val = prfs; opaque_dir = odp; _ } = function
  | Direct (_,cu) ->
    Future.force cu
  | Indirect (l,dp,i) ->
    let pt, u =
      if DirPath.equal dp odp
      then Future.force (snd (Int.Map.find i prfs))
      else Future.force (get_opaque tbl dp i), Univ.ContextSet.empty in
    force_constr (List.fold_right subst_substituted l (from_val pt)), u

let get_cst tbl { opaque_val = prfs; opaque_dir = odp; _ } = function
  | Direct (_,cu) -> cu
  | Indirect (l,dp,i) ->
    let pt =
      if DirPath.equal dp odp
      then snd (Int.Map.find i prfs)
      else Future.chain (get_opaque tbl dp i) (fun c -> c, Univ.ContextSet.empty) in
    Future.chain pt (fun (c, u) ->
        force_constr (List.fold_right subst_substituted l (from_val c)), u)

module FMap = Future.UUIDMap

let a_constr = Future.from_val (mkRel 1)
let a_univ = Future.from_val Univ.ContextSet.empty
let a_discharge : cooking_info list = []

let dump { opaque_val = otab; opaque_len = n; _ } =
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
