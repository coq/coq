(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Genarg
open Pp
open Names
open Tacexpr

(** Tactic notations (TacAlias) *)

type alias = KerName.t

let alias_map = Summary.ref ~name:"tactic-alias"
  (KNmap.empty : glob_tactic_expr KNmap.t)

let register_alias key tac =
  alias_map := KNmap.add key tac !alias_map

let interp_alias key =
  try KNmap.find key !alias_map
  with Not_found -> Errors.anomaly (str "Unknown tactic alias: " ++ KerName.print key)

(** ML tactic extensions (TacML) *)

type ml_tactic =
  typed_generic_argument list -> Geninterp.interp_sign -> unit Proofview.tactic

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
  t.mltac_plugin ^ "::" ^ t.mltac_tactic

let tac_tab = ref MLTacMap.empty

let register_ml_tactic ?(overwrite = false) s (t : ml_tactic) =
  let () =
    if MLTacMap.mem s !tac_tab then
      if overwrite then
        let () = tac_tab := MLTacMap.remove s !tac_tab in
        msg_warning (str ("Overwriting definition of tactic " ^ pr_tacname s))
      else
        Errors.anomaly (str ("Cannot redeclare tactic " ^ pr_tacname s ^ "."))
  in
  tac_tab := MLTacMap.add s t !tac_tab

let interp_ml_tactic { mltac_name = s } =
  try
    MLTacMap.find s !tac_tab
  with Not_found ->
    Errors.errorlabstrm ""
      (str "The tactic " ++ str (pr_tacname s) ++ str " is not installed.")

(***************************************************************************)
(* Tactic registration *)

(* Summary and Object declaration *)

open Nametab
open Libnames
open Libobject

let mactab =
  Summary.ref (KNmap.empty : (bool * glob_tactic_expr) KNmap.t)
    ~name:"tactic-definition"

let interp_ltac r = snd (KNmap.find r !mactab)

let is_ltac_for_ml_tactic r = fst (KNmap.find r !mactab)

(* Declaration of the TAC-DEFINITION object *)
let add (kn,td) = mactab := KNmap.add kn td !mactab
let replace (kn,td) = mactab := KNmap.add kn td !mactab

let load_md i ((sp, kn), (local, id, b, t)) = match id with
| None ->
  let () = if not local then Nametab.push_tactic (Until i) sp kn in
  add (kn, (b,t))
| Some kn -> add (kn, (b,t))

let open_md i ((sp, kn), (local, id, b, t)) = match id with
| None ->
  let () = if not local then Nametab.push_tactic (Exactly i) sp kn in
  add (kn, (b,t))
| Some kn -> add (kn, (b,t))

let cache_md ((sp, kn), (local, id ,b, t)) = match id with
| None ->
  let () = Nametab.push_tactic (Until 1) sp kn in
  add (kn, (b,t))
| Some kn -> add (kn, (b,t))

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
