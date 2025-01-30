(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
    alias_deprecation: Deprecation.t option;
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

open Libobject

type ltac_entry = {
  tac_for_ml : bool;
  tac_body : glob_tactic_expr;
  tac_redef : ModPath.t list;
  tac_deprecation : Deprecation.t option
}

let mactab =
  Summary.ref (KNmap.empty : ltac_entry KNmap.t)
    ~name:"tactic-definition"

let ltac_entries () = !mactab

let interp_ltac r = (KNmap.find r !mactab).tac_body

let is_ltac_for_ml_tactic r = (KNmap.find r !mactab).tac_for_ml

let add ~depr kn b t =
  let entry = {
    tac_for_ml = b;
    tac_body = t;
    tac_redef = [];
    tac_deprecation = depr;
  }
  in
  mactab := KNmap.add kn entry !mactab

let replace kn path t =
  let entry _ e = { e with tac_body = t; tac_redef = path :: e.tac_redef } in
  mactab := KNmap.modify kn entry !mactab

let tac_deprecation kn =
  try (KNmap.find kn !mactab).tac_deprecation with Not_found -> None

type tacdef = {
  local : bool;
  id : Id.t;
  for_ml : bool;
  expr : glob_tactic_expr;
  depr : Deprecation.t option;
}

let load_md i (prefix, {local; id; for_ml=b; expr=t; depr}) =
  let sp, kn = Lib.make_oname prefix id in
  let () = if not local then push_tactic (Nametab.Until i) sp kn in
  add ~depr kn b t

let open_md i (prefix, {local; id; for_ml=b; expr=t; depr}) =
  (* todo: generate a warning when non-unique, record choices for non-unique mappings *)
  let sp, kn = Lib.make_oname prefix id in
  let () = if not local then push_tactic (Nametab.Exactly i) sp kn in
  add ~depr kn b t

let cache_md (prefix, {local; id; for_ml=b; expr=t; depr}) =
  let sp, kn = Lib.make_oname prefix id in
  let () = push_tactic (Nametab.Until 1) sp kn in
  add ~depr kn b t

let subst_md (subst, {local; id; for_ml; expr=t; depr}) =
  {local; id; for_ml; expr=Tacsubst.subst_tactic subst t; depr}

let classify_md _ = Substitute

let inMD : tacdef -> obj =
  declare_named_object_gen {(default_object "TAC-DEFINITION") with
     cache_function = cache_md;
     load_function = load_md;
     open_function = simple_open open_md;
     subst_function = subst_md;
     classify_function = classify_md}

let register_ltac for_ml local ?deprecation id tac =
  Lib.add_leaf (inMD {local; id; for_ml; expr=tac; depr=deprecation})

type tacreplace = {
  repl_local : Libobject.locality;
  repl_tac : ltac_constant;
  repl_expr : glob_tactic_expr;
}

let load_replace i (prefix, {repl_local; repl_tac; repl_expr=t}) =
  match repl_local with
  | Local | Export -> ()
  | SuperGlobal ->
    replace repl_tac prefix.Nametab.obj_mp t

let open_replace i (prefix, {repl_local; repl_tac; repl_expr=t}) =
  match repl_local with
  | Local | SuperGlobal -> ()
  | Export ->
    replace repl_tac prefix.Nametab.obj_mp t

let cache_replace (prefix, {repl_local; repl_tac; repl_expr=t}) =
  replace repl_tac prefix.Nametab.obj_mp t

let subst_replace (subst, {repl_local; repl_tac; repl_expr}) =
  { repl_local;
    repl_tac=Mod_subst.subst_kn subst repl_tac;
    repl_expr=Tacsubst.subst_tactic subst repl_expr;
  }

let classify_replace o = match o.repl_local with
  | Local -> Dispose
  | Export | SuperGlobal -> Substitute

let inReplace : tacreplace -> obj =
  declare_named_object_gen {(default_object "TAC-REDEFINITION") with
     cache_function = cache_replace;
     load_function = load_replace;
     open_function = simple_open open_replace;
     subst_function = subst_replace;
     classify_function = classify_replace}

let redefine_ltac repl_local repl_tac repl_expr =
  Lib.add_leaf (inReplace {repl_local; repl_tac; repl_expr})
