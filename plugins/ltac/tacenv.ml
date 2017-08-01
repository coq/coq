(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Pp
open Names
open Tacexpr

(** Tactic notations (TacAlias) *)

type alias = KerName.t
type alias_tactic = Id.t list * glob_tactic_expr

let alias_map = Summary.ref ~name:"tactic-alias"
  (KNmap.empty : alias_tactic KNmap.t)

let register_alias key tac =
  alias_map := KNmap.add key tac !alias_map

let interp_alias key =
  try KNmap.find key !alias_map
  with Not_found -> CErrors.anomaly (str "Unknown tactic alias: " ++ KerName.print key ++ str ".")

let check_alias key = KNmap.mem key !alias_map

(** ML tactic extensions (TacML) *)

type ml_tactic =
  Geninterp.Val.t list -> Geninterp.interp_sign -> unit Proofview.tactic

module MLName =
struct
  type t = ml_tactic_name
  let compare tac1 tac2 =
    let c = String.compare tac1.mltac_tactic tac2.mltac_tactic in
    if c = 0 then String.compare tac1.mltac_plugin tac2.mltac_plugin
    else c
end

module MLTacMap = Map.Make(MLName)

let pr_tacname t =
  str t.mltac_plugin ++ str "::" ++ str t.mltac_tactic

let tac_tab = ref MLTacMap.empty

let register_ml_tactic ?(overwrite = false) s (t : ml_tactic array) =
  let () =
    if MLTacMap.mem s !tac_tab then
      if overwrite then
        tac_tab := MLTacMap.remove s !tac_tab
      else
        CErrors.anomaly (str "Cannot redeclare tactic " ++ pr_tacname s ++ str ".")
  in
  tac_tab := MLTacMap.add s t !tac_tab

let interp_ml_tactic { mltac_name = s; mltac_index = i } =
  try
    let tacs = MLTacMap.find s !tac_tab in
    let () = if Array.length tacs <= i then raise Not_found in
    tacs.(i)
  with Not_found ->
    CErrors.user_err 
      (str "The tactic " ++ pr_tacname s ++ str " is not installed.")

(***************************************************************************)
(* Tactic registration *)

(* Summary and Object declaration *)

open Nametab
open Libobject

type ltac_entry = {
  tac_for_ml : bool;
  tac_body : glob_tactic_expr;
  tac_redef : ModPath.t list;
}

let mactab =
  Summary.ref (KNmap.empty : ltac_entry KNmap.t)
    ~name:"tactic-definition"

let ltac_entries () = !mactab

let interp_ltac r = (KNmap.find r !mactab).tac_body

let is_ltac_for_ml_tactic r = (KNmap.find r !mactab).tac_for_ml

let add kn b t =
  let entry = { tac_for_ml = b; tac_body = t; tac_redef = [] } in
  mactab := KNmap.add kn entry !mactab

let replace kn path t =
  let (path, _, _) = KerName.repr path in
  let entry _ e = { e with tac_body = t; tac_redef = path :: e.tac_redef } in
  mactab := KNmap.modify kn entry !mactab

let load_md i ((sp, kn), (local, id, b, t)) = match id with
| None ->
  let () = if not local then Nametab.push_tactic (Until i) sp kn in
  add kn b t
| Some kn0 -> replace kn0 kn t

let open_md i ((sp, kn), (local, id, b, t)) = match id with
| None ->
  let () = if not local then Nametab.push_tactic (Exactly i) sp kn in
  add kn b t
| Some kn0 -> replace kn0 kn t

let cache_md ((sp, kn), (local, id ,b, t)) = match id with
| None ->
  let () = Nametab.push_tactic (Until 1) sp kn in
  add kn b t
| Some kn0 -> replace kn0 kn t

let subst_kind subst id = match id with
| None -> None
| Some kn -> Some (Mod_subst.subst_kn subst kn)

let subst_md (subst, (local, id, b, t)) =
  (local, subst_kind subst id, b, Tacsubst.subst_tactic subst t)

let classify_md (local, _, _, _ as o) = Substitute o

let inMD : bool * Nametab.ltac_constant option * bool * glob_tactic_expr -> obj =
  declare_object {(default_object "TAC-DEFINITION") with
     cache_function  = cache_md;
     load_function   = load_md;
     open_function   = open_md;
     subst_function = subst_md;
     classify_function = classify_md}

let register_ltac for_ml local id tac =
  ignore (Lib.add_leaf id (inMD (local, None, for_ml, tac)))

let redefine_ltac local kn tac =
  Lib.add_anonymous_leaf (inMD (local, Some kn, false, tac))
