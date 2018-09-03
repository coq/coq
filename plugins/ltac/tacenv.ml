(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Pp
open Names
open Tacexpr

(** Nametab for tactics *)

(** TODO: Share me somewhere *)
module FullPath =
struct
  open Libnames
  type t = full_path
  let equal = eq_full_path
  let to_string = string_of_path
  let repr sp =
    let dir,id = repr_path sp in
      id, (DirPath.repr dir)
end

module KnTab = Nametab.Make(FullPath)(KerName)

let tactic_tab = Summary.ref ~name:"LTAC-NAMETAB" (KnTab.empty, KNmap.empty)

let push_tactic vis sp kn =
  let (tab, revtab) = !tactic_tab in
  let tab = KnTab.push vis sp kn tab in
  let revtab = KNmap.add kn sp revtab in
  tactic_tab := (tab, revtab)

let locate_tactic qid = KnTab.locate qid (fst !tactic_tab)

let locate_extended_all_tactic qid = KnTab.find_prefixes qid (fst !tactic_tab)

let exists_tactic kn = KnTab.exists kn (fst !tactic_tab)

let path_of_tactic kn = KNmap.find kn (snd !tactic_tab)

let shortest_qualid_of_tactic kn =
  let sp = KNmap.find kn (snd !tactic_tab) in
  KnTab.shortest_qualid Id.Set.empty sp (fst !tactic_tab)

(** Tactic notations (TacAlias) *)

type alias = KerName.t
type alias_tactic =
  { alias_args: Id.t list;
    alias_body: glob_tactic_expr;
    alias_deprecation: Vernacinterp.deprecation option;
  }

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
  tac_deprecation : Vernacinterp.deprecation option
}

let mactab =
  Summary.ref (KNmap.empty : ltac_entry KNmap.t)
    ~name:"tactic-definition"

let ltac_entries () = !mactab

let interp_ltac r = (KNmap.find r !mactab).tac_body

let is_ltac_for_ml_tactic r = (KNmap.find r !mactab).tac_for_ml

let add ~deprecation kn b t =
  let entry = { tac_for_ml = b;
                tac_body = t;
                tac_redef = [];
                tac_deprecation = deprecation;
              } in
  mactab := KNmap.add kn entry !mactab

let replace kn path t =
  let path = KerName.modpath path in
  let entry _ e = { e with tac_body = t; tac_redef = path :: e.tac_redef } in
  mactab := KNmap.modify kn entry !mactab

let tac_deprecation kn =
  try (KNmap.find kn !mactab).tac_deprecation with Not_found -> None

let load_md i ((sp, kn), (local, id, b, t, deprecation)) = match id with
| None ->
  let () = if not local then push_tactic (Until i) sp kn in
  add ~deprecation kn b t
| Some kn0 -> replace kn0 kn t

let open_md i ((sp, kn), (local, id, b, t, deprecation)) = match id with
| None ->
  let () = if not local then push_tactic (Exactly i) sp kn in
  add ~deprecation kn b t
| Some kn0 -> replace kn0 kn t

let cache_md ((sp, kn), (local, id ,b, t, deprecation)) = match id with
| None ->
  let () = push_tactic (Until 1) sp kn in
  add ~deprecation kn b t
| Some kn0 -> replace kn0 kn t

let subst_kind subst id = match id with
| None -> None
| Some kn -> Some (Mod_subst.subst_kn subst kn)

let subst_md (subst, (local, id, b, t, deprecation)) =
  (local, subst_kind subst id, b, Tacsubst.subst_tactic subst t, deprecation)

let classify_md (local, _, _, _, _ as o) = Substitute o

let inMD : bool * ltac_constant option * bool * glob_tactic_expr *
           Vernacinterp.deprecation option -> obj =
  declare_object {(default_object "TAC-DEFINITION") with
     cache_function  = cache_md;
     load_function   = load_md;
     open_function   = open_md;
     subst_function = subst_md;
     classify_function = classify_md}

let register_ltac for_ml local ?deprecation id tac =
  ignore (Lib.add_leaf id (inMD (local, None, for_ml, tac, deprecation)))

let redefine_ltac local ?deprecation kn tac =
  Lib.add_anonymous_leaf (inMD (local, Some kn, false, tac, deprecation))
